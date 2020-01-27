"""Dependency Resolution

The dependency resolution in pip is performed as follows:

for top-level requirements:
    a. only one spec allowed per project, regardless of conflicts or not.
       otherwise a "double requirement" exception is raised
    b. they override sub-dependency requirements.
for sub-dependencies
    a. "first found, wins" (where the order is breadth first)
"""

# The following comment should be removed at some point in the future.
# mypy: strict-optional=False
# mypy: disallow-untyped-defs=False

import logging
import queue
import re
import struct
import sys
import zlib
from collections import defaultdict
from contextlib import contextmanager
from itertools import chain
from threading import Thread
from typing import Any

from pip._vendor.packaging import specifiers, version
from pip._vendor.packaging.requirements import Requirement

from pip._internal.distributions.base import AbstractDistribution
from pip._internal.exceptions import (
    BestVersionAlreadyInstalled,
    DistributionNotFound,
    HashError,
    HashErrors,
    UnsupportedPythonVersion,
)
from pip._internal.req.req_install import InstallRequirement
from pip._internal.req.req_set import VersionConflictError
from pip._internal.utils.logging import indent_log
from pip._internal.utils.misc import (
    dist_in_usersite,
    ensure_dir,
    normalize_version_info,
)
from pip._internal.utils.packaging import (
    check_requires_python,
    get_requires_python,
)
from pip._internal.utils.typing import MYPY_CHECK_RUNNING
from pip._internal.util.urls import get_url_scheme

if MYPY_CHECK_RUNNING:
    from typing import Callable, DefaultDict, List, Optional, Set, Tuple
    from pip._vendor import pkg_resources

    from pip._internal.distributions import AbstractDistribution
    from pip._internal.index.package_finder import PackageFinder
    from pip._internal.network.session import PipSession
    from pip._internal.index import PackageFinder
    from pip._internal.operations.prepare import RequirementPreparer
    from pip._internal.req.req_set import RequirementSet

    InstallRequirementProvider = Callable[
        [str, InstallRequirement], InstallRequirement
    ]
    DiscoveredDependencies = DefaultDict[str, List[InstallRequirement]]

logger = logging.getLogger(__name__)


def _check_dist_requires_python(
    dist,  # type: pkg_resources.Distribution
    version_info,  # type: Tuple[int, int, int]
    ignore_requires_python=False,  # type: bool
):
    # type: (...) -> None
    """
    Check whether the given Python version is compatible with a distribution's
    "Requires-Python" value.

    :param version_info: A 3-tuple of ints representing the Python
        major-minor-micro version to check.
    :param ignore_requires_python: Whether to ignore the "Requires-Python"
        value if the given Python version isn't compatible.

    :raises UnsupportedPythonVersion: When the given Python version isn't
        compatible.
    """
    requires_python = get_requires_python(dist)
    try:
        is_compatible = check_requires_python(
            requires_python, version_info=version_info,
        )
    except specifiers.InvalidSpecifier as exc:
        logger.warning(
            "Package %r has an invalid Requires-Python: %s",
            dist.project_name, exc,
        )
        return

    if is_compatible:
        return

    version = '.'.join(map(str, version_info))
    if ignore_requires_python:
        logger.debug(
            'Ignoring failed Requires-Python check for package %r: '
            '%s not in %r',
            dist.project_name, version, requires_python,
        )
        return

    raise UnsupportedPythonVersion(
        'Package {!r} requires a different Python: {} not in {!r}'.format(
            dist.project_name, version, requires_python,
        ))


class LazyDistribution(AbstractDistribution):

    def has_been_downloaded(self):
        return False

    def get_pkg_resources_distribution(self):
        raise NotImplementedError('!!!!')

    def prepare_distribution_metadata(self, finder, build_isolation):
        raise NotImplementedError('????')


# From https://stackoverflow.com/a/1089787/2518889:
def _inflate(data):
    decompress = zlib.decompressobj(-zlib.MAX_WBITS)
    inflated = decompress.decompress(data)
    inflated += decompress.flush()
    return inflated


def _decode_4_byte_unsigned(byte_string):
    """Unpack as a little-endian unsigned long."""
    assert isinstance(byte_string, bytes) and len(byte_string) == 4, byte_string
    return struct.unpack('<L', byte_string)[0]


def _decode_2_byte_unsigned(byte_string):
    """Unpack as a little-endian unsigned short."""
    assert isinstance(byte_string, bytes) and len(byte_string) == 2
    return struct.unpack('<H', byte_string)[0]


class _RequirementSubset(object):
    """A component of the concurrent sub-global resolves used with quickly_parse_sub_requirements=True."""

    def __init__(self, priority, item):
        self.priority = priority
        self.item = item

    def __lt__(self, other):
        assert isinstance(other, _RequirementSubset)
        return self.priority < other.priority

    @classmethod
    def create(cls, req_set, *args):
        return cls(priority=req_set.rank(),
                   item=((req_set,) + args))


class _MetadataResolveMapping(object):
    """Keep an updated, ordered mapping of all transitively resolved requirements."""

    def __init__(self, resolver):
        self._resolver = resolver
        # See https://docs.python.org/3/library/queue.html#queue.PriorityQueue!
        self._without_links = queue.PriorityQueue()
        self._with_links = queue.PriorityQueue()
        self._inflight = queue.PriorityQueue()
        self._completing = queue.Queue(maxsize=1)
        self._subthread_errors = []
        self._failed_resolves = []
        self._successes = queue.Queue()

        self._num_iterations = 0

    def _wrap_subthread_fn(self, indentation, invoke_fn, requirement_set, req):
        from pip._internal.utils.logging import _log_state
        _log_state.indentation = indentation

        try:
            invoke_fn(requirement_set, req)
        except Exception as e:
            self._subthread_errors.append((requirement_set, req, e))
        finally:
            self._completing.put(())

    def _populate_link(self, requirement_set, req):
        assert not req.link
        logger.warn(f'(#{self._num_iterations}) populating link for req {req} in {requirement_set}')

        # We're collapsing the waveform in this thread. Make a copy in order to avoid making greedy
        # decisions, with a link back to the parent requirement set.
        requirement_set = requirement_set.copy()
        # req = req.copy()

        # Tell user what we are doing for this requirement:
        # obtain (editable), skipping, processing (local url), collecting
        # (remote url or package name)
        if req.constraint or req.prepared:
            return

        req.prepared = True

        # register tmp src for cleanup in case something goes wrong
        requirement_set.reqs_to_cleanup.append(req)

        assert self._resolver.require_hashes is not None, (
            "require_hashes should have been set in Resolver.resolve()"
        )

        if req.editable:
            return self._resolver.preparer.prepare_editable_requirement(
                req, self._resolver.require_hashes, self._resolver.use_user_site,
                self._resolver.finder)

        # satisfied_by is only evaluated by calling _check_skip_installed,
        # so it must be None here.
        assert req.satisfied_by is None
        skip_reason = self._resolver._check_skip_installed(req)

        if req.satisfied_by:
            return self._resolver.preparer.prepare_installed_requirement(
                req, self._resolver.require_hashes, skip_reason
            )

        upgrade_allowed = self._resolver._is_upgrade_allowed(req)

        # We eagerly populate the link, since that's our "legacy" behavior.
        req.populate_link(self._resolver.finder, upgrade_allowed, self._resolver.require_hashes)
        assert req.link

        self._with_links.put_nowait(_RequirementSubset.create(requirement_set, req))

    def _make_inflight_waiter_thread(self):
        def wait_to_extract_thread():
            while True:
                try:
                    entry = self._inflight.get()
                    req_set, req, inflight_thread = entry.item
                    logger.warn(f'priority: {entry.priority}, item: {entry.item}')

                    # Check that it hasn't been started yet.
                    assert inflight_thread.ident is None
                    inflight_thread.start()

                    _ = self._completing.get()
                except (DistributionNotFound, VersionConflictError) as e:
                    self._failed_resolves.append((req_set, req, e))
                except Exception as e:
                    self._subthread_errors.append((item, e))
        return Thread(name=f'waiter for the in-flight queue!',
                      target=wait_to_extract_thread,
                      daemon=True)

    def _toplevel_event_loop(self):
        waiter_thread = self._make_inflight_waiter_thread()
        # We leak this thread.
        waiter_thread.start()

        while True:
            self._num_iterations += 1
            if self._subthread_errors:
                # NB: This just gets the most recent of the errors!
                req_set, req, e = self._subthread_errors.pop()
                raise Exception(f'failed to resolve {req} from {req_set}: {e}') from e

            try:
                while True:
                    yield self._successes.get_nowait()
            except queue.Empty:
                pass

            try:
                while True:
                    req_set, no_link_req = self._without_links.get_nowait().item
                    from pip._internal.utils.logging import _log_state
                    link_thread = Thread(name=f'pip populate link background thread: {no_link_req} for {req_set}',
                                         target=self._wrap_subthread_fn,
                                         args=(
                                             _log_state.indentation,
                                             self._populate_link,
                                             req_set,
                                             no_link_req,
                                         ),
                                         daemon=True)
                    self._inflight.put(_RequirementSubset.create(req_set, no_link_req, link_thread))
            except queue.Empty:
                pass

            try:
                while True:
                    req_set, link_req = self._with_links.get_nowait().item
                    from pip._internal.utils.logging import _log_state
                    resolve_thread = Thread(name=f'pip resolve background thread: {link_req} for {req_set}',
                                            target=self._wrap_subthread_fn,
                                            args=(
                                                _log_state.indentation,
                                                self._spawn_subjob,
                                                req_set,
                                                link_req,
                                            ),
                                            daemon=True)
                    self._inflight.put(_RequirementSubset.create(req_set, link_req, resolve_thread))
            except queue.Empty:
                pass

    def _accept_new_reqs(self, requirement_set, reqs):
        for root_req in reqs:
            if root_req.name in ['functools32', 'nodeenv']:
                continue
            if root_req.force_eager_download:
                assert root_req.link
                # NB: this is where we would download the wheels in a pipelined resolve + fetch, but
                # we just want the transitive requirements.
            else:
              assert not root_req.link
              self._without_links.put_nowait(_RequirementSubset.create(requirement_set, root_req))

        if requirement_set.resolve_has_been_completed():
            self._successes.put(requirement_set)

    def _spawn_subjob(self, req_set, link_req):
        logger.warn(f'(#{self._num_iterations}) resolving linked req {link_req} in {req_set}')
        self._accept_new_reqs(req_set, self._resolver._resolve_one(req_set.copy(), link_req.copy()))

    def iterate_until_fully_resolved(self, requirement_set):
        self._accept_new_reqs(requirement_set, requirement_set.as_root_reqs())

        yield from self._toplevel_event_loop()


class MetadataOnlyResolveException(Exception):
    """Exception used for control flow to return a result quickly to a user of pip-as-a-library!"""

    def __init__(self, requirements):
        super().__init__(f'resolved requirements: {requirements}')
        self.requirements = requirements


class Resolver(object):
    """Resolves which packages need to be installed/uninstalled to perform \
    the requested operation without breaking the requirements of any package.
    """

    _allowed_strategies = {"eager", "only-if-needed", "to-satisfy-only"}

    def __init__(
        self,
        preparer,  # type: RequirementPreparer
        finder,  # type: PackageFinder
        make_install_req,  # type: InstallRequirementProvider
        use_user_site,  # type: bool
        ignore_dependencies,  # type: bool
        ignore_installed,  # type: bool
        ignore_requires_python,  # type: bool
        force_reinstall,  # type: bool
        upgrade_strategy,  # type: str
        py_version_info=None,  # type: Optional[Tuple[int, ...]]
        quickly_parse_sub_requirements=False, # type: bool
    ):
        # type: (...) -> None
        super(Resolver, self).__init__()
        assert upgrade_strategy in self._allowed_strategies

        if py_version_info is None:
            py_version_info = sys.version_info[:3]
        else:
            py_version_info = normalize_version_info(py_version_info)

        self._py_version_info = py_version_info

        self.preparer = preparer
        self.finder = finder

        self.upgrade_strategy = upgrade_strategy
        self.force_reinstall = force_reinstall
        self.ignore_dependencies = ignore_dependencies
        self.ignore_installed = ignore_installed
        self.ignore_requires_python = ignore_requires_python
        self.use_user_site = use_user_site
        self._make_install_req = make_install_req

        self._discovered_dependencies = \
            defaultdict(list)  # type: DiscoveredDependencies

        self.quickly_parse_sub_requirements = quickly_parse_sub_requirements

    def resolve(self, requirement_set):
        # type: (RequirementSet) -> None
        """Resolve what operations need to be done

        As a side-effect of this method, the packages (and their dependencies)
        are downloaded, unpacked and prepared for installation. This
        preparation is done by ``pip.operations.prepare``.

        Once PyPI has static dependency metadata available, it would be
        possible to move the preparation to become a step separated from
        dependency resolution.
        """
        # make the wheelhouse
        if self.preparer.wheel_download_dir:
            ensure_dir(self.preparer.wheel_download_dir)

        # If any top-level requirement has a hash specified, enter
        # hash-checking mode, which requires hashes from all.

        root_reqs = requirement_set.as_root_reqs()

        # Display where finder is looking for packages
        search_scope = self.finder.search_scope
        locations = search_scope.get_formatted_locations()
        if locations:
            logger.info(locations)

        # Actually prepare the files, and collect any exceptions. Most hash
        # exceptions cannot be checked ahead of time, because
        # req.populate_link() needs to be called before we can make decisions
        # based on link type.
        discovered_reqs = []    # type: List[InstallRequirement]
        hash_errors = HashErrors()

        if self.quickly_parse_sub_requirements:
            metadata_mapping = _MetadataResolveMapping(self)
            for completed_req_set in metadata_mapping.iterate_until_fully_resolved(requirement_set):
                raise MetadataOnlyResolveException(completed_req_set.as_root_reqs())
            raise ValueError(f'only found failures: {metadata_mapping._failed_resolves}')

        for req in chain(root_reqs, discovered_reqs):
            try:
                discovered_reqs.extend(self._resolve_one(requirement_set, req))
            except HashError as exc:
                exc.req = req
                hash_errors.append(exc)

        if hash_errors:
            raise hash_errors

    def _is_upgrade_allowed(self, req):
        # type: (InstallRequirement) -> bool
        if self.upgrade_strategy == "to-satisfy-only":
            return False
        elif self.upgrade_strategy == "eager":
            return True
        else:
            assert self.upgrade_strategy == "only-if-needed"
            return req.is_direct

    def _set_req_to_reinstall(self, req):
        # type: (InstallRequirement) -> None
        """
        Set a requirement to be installed.
        """
        # Don't uninstall the conflict if doing a user install and the
        # conflict is not a user install.
        if not self.use_user_site or dist_in_usersite(req.satisfied_by):
            req.should_reinstall = True
        req.satisfied_by = None

    def _check_skip_installed(self, req_to_install):
        # type: (InstallRequirement) -> Optional[str]
        """Check if req_to_install should be skipped.

        This will check if the req is installed, and whether we should upgrade
        or reinstall it, taking into account all the relevant user options.

        After calling this req_to_install will only have satisfied_by set to
        None if the req_to_install is to be upgraded/reinstalled etc. Any
        other value will be a dist recording the current thing installed that
        satisfies the requirement.

        Note that for vcs urls and the like we can't assess skipping in this
        routine - we simply identify that we need to pull the thing down,
        then later on it is pulled down and introspected to assess upgrade/
        reinstalls etc.

        :return: A text reason for why it was skipped, or None.
        """
        if self.ignore_installed:
            return None

        req_to_install.check_if_exists(self.use_user_site)
        if not req_to_install.satisfied_by:
            return None

        if self.force_reinstall:
            self._set_req_to_reinstall(req_to_install)
            return None

        if not self._is_upgrade_allowed(req_to_install):
            if self.upgrade_strategy == "only-if-needed":
                return 'already satisfied, skipping upgrade'
            return 'already satisfied'

        # Check for the possibility of an upgrade.  For link-based
        # requirements we have to pull the tree down and inspect to assess
        # the version #, so it's handled way down.
        if not req_to_install.link:
            try:
                self.finder.find_requirement(req_to_install, upgrade=True)
            except BestVersionAlreadyInstalled:
                # Then the best version is installed.
                return 'already up-to-date'
            except DistributionNotFound:
                # No distribution found, so we squash the error.  It will
                # be raised later when we re-try later to do the install.
                # Why don't we just raise here?
                pass

        self._set_req_to_reinstall(req_to_install)
        return None

    def _get_abstract_dist_for(self, req):
        # type: (InstallRequirement) -> AbstractDistribution
        """Takes a InstallRequirement and returns a single AbstractDist \
        representing a prepared variant of the same.
        """
        if req.editable:
            return self.preparer.prepare_editable_requirement(req)

        # satisfied_by is only evaluated by calling _check_skip_installed,
        # so it must be None here.
        assert req.satisfied_by is None
        skip_reason = self._check_skip_installed(req)

        if req.satisfied_by:
            return self.preparer.prepare_installed_requirement(
                req, skip_reason
            )

        upgrade_allowed = self._is_upgrade_allowed(req)

        # We eagerly populate the link, since that's our "legacy" behavior.
        require_hashes = self.preparer.require_hashes

        req.populate_link(self.finder, upgrade_allowed, require_hashes)

        # If we've been configured to hack out the METADATA file from a remote wheel, extract sub
        # requirements first!
        if self.quickly_parse_sub_requirements and (not req.force_eager_download) and req.link.is_wheel:
            return LazyDistribution(req)

        abstract_dist = self.preparer.prepare_linked_requirement(req)

        # NOTE
        # The following portion is for determining if a certain package is
        # going to be re-installed/upgraded or not and reporting to the user.
        # This should probably get cleaned up in a future refactor.

        # req.req is only avail after unpack for URL
        # pkgs repeat check_if_exists to uninstall-on-upgrade
        # (#14)
        if not self.ignore_installed:
            req.check_if_exists(self.use_user_site)

        if req.satisfied_by:
            should_modify = (
                self.upgrade_strategy != "to-satisfy-only" or
                self.force_reinstall or
                self.ignore_installed or
                req.link.scheme == 'file'
            )
            if should_modify:
                self._set_req_to_reinstall(req)
            else:
                logger.info(
                    'Requirement already satisfied (use --upgrade to upgrade):'
                    ' %s', req,
                )

        return abstract_dist

    def _hacky_extract_sub_reqs(self, req):
        """Obtain the dependencies of a wheel requirement by scanning the METADATA file."""
        url = str(req.link)
        scheme = get_url_scheme(url)
        assert scheme in ['http', 'https']

        head_resp = self.session.head(url)
        head_resp.raise_for_status()
        assert 'bytes' in head_resp.headers['Accept-Ranges']
        wheel_content_length = int(head_resp.headers['Content-Length'])

        shallow_begin = max(wheel_content_length - 2000, 0)
        wheel_shallow_resp = self.session.get(url, headers={
            'Range': f'bytes={shallow_begin}-{wheel_content_length}',
        })
        wheel_shallow_resp.raise_for_status()
        if wheel_content_length <= 2000:
            last_2k_bytes = wheel_shallow_resp.content
        else:
            assert len(wheel_shallow_resp.content) >= 2000
            last_2k_bytes = wheel_shallow_resp.content[-2000:]

        sanitized_requirement_name = req.name.lower().replace('-', '_')
        metadata_file_pattern = f'{sanitized_requirement_name}[^/]+?.dist-info/METADATAPK'.encode()
        filename_in_central_dir_header = re.search(metadata_file_pattern, last_2k_bytes,
                                                   flags=re.IGNORECASE)
        try:
            _st = filename_in_central_dir_header.start()
        except AttributeError as e:
            raise Exception(f'req: {req}, pat: {metadata_file_pattern}, len(b): {len(last_2k_bytes)}') from e

        encoded_offset_for_local_file = last_2k_bytes[(_st - 4):_st]
        _off = _decode_4_byte_unsigned(encoded_offset_for_local_file)

        local_file_header_resp = self.session.get(url, headers={
            'Range': f'bytes={_off+18}-{_off+30}',
        })
        local_file_header_resp.raise_for_status()

        if len(local_file_header_resp.content) == 13:
            file_header_no_filename = local_file_header_resp.content[:12]
        elif len(local_file_header_resp.content) > 12:
            file_header_no_filename = local_file_header_resp.content[(_off + 18):(_off + 30)]
        else:
            file_header_no_filename = local_file_header_resp.content

        try:
            compressed_size = _decode_4_byte_unsigned(file_header_no_filename[:4])
        except AssertionError as e:
            raise Exception(f'c: {local_file_header_resp.content}, _off: {_off}') from e
        uncompressed_size = _decode_4_byte_unsigned(file_header_no_filename[4:8])
        file_name_length = _decode_2_byte_unsigned(file_header_no_filename[8:10])
        assert file_name_length == (len(filename_in_central_dir_header.group(0)) - 2)
        extra_field_length = _decode_2_byte_unsigned(file_header_no_filename[10:12])
        compressed_start = _off + 30 + file_name_length + extra_field_length
        compressed_end = compressed_start + compressed_size

        metadata_file_resp = self.session.get(url, headers={
            'Range': f'bytes={compressed_start}-{compressed_end}',
        })
        metadata_file_resp.raise_for_status()

        if len(metadata_file_resp.content) == len(local_file_header_resp.content):
            metadata_file_bytes = metadata_file_resp.content[compressed_start:compressed_end]
        else:
            metadata_file_bytes = metadata_file_resp.content[:compressed_size]

        try:
            uncompressed_file_contents = _inflate(metadata_file_bytes)
        except zlib.error as e:
            logger.exception(e)
            import pdb; pdb.set_trace()

        assert len(uncompressed_file_contents) == uncompressed_size

        decoded_metadata_file = uncompressed_file_contents.decode('utf-8')
        all_requirements = [
            Requirement(re.sub(r'^(.*) \((.*)\)$', r'\1\2', g[1]))
            for g in re.finditer(r'^Requires-Dist: (.*)$', decoded_metadata_file, flags=re.MULTILINE)
        ]
        return [
            self._make_install_req(
                str(subreq),
                comes_from=req,
            ) for subreq in all_requirements
        ]

    def _resolve_one(
        self,
        requirement_set,  # type: RequirementSet
        req_to_install,  # type: InstallRequirement
    ):
        # type: (...) -> List[InstallRequirement]
        """Prepare a single requirements file.

        :return: A list of additional InstallRequirements to also install.
        """
        # Tell user what we are doing for this requirement:
        # obtain (editable), skipping, processing (local url), collecting
        # (remote url or package name)
        if req_to_install.constraint or req_to_install.prepared:
            return []

        req_to_install.prepared = True

        # register tmp src for cleanup in case something goes wrong
        requirement_set.reqs_to_cleanup.append(req_to_install)

        abstract_dist = self._get_abstract_dist_for(req_to_install)

        if not abstract_dist.has_been_downloaded():
            sub_reqs = self._hacky_extract_sub_reqs(abstract_dist.req)
            req_to_install.force_eager_download = True
            return [
                *sub_reqs,
                req_to_install,
            ]

        abstract_dist.req.has_backing_dist = True

        # Parse and return dependencies
        dist = abstract_dist.get_pkg_resources_distribution()
        # This will raise UnsupportedPythonVersion if the given Python
        # version isn't compatible with the distribution's Requires-Python.
        _check_dist_requires_python(
            dist, version_info=self._py_version_info,
            ignore_requires_python=self.ignore_requires_python,
        )

        more_reqs = []  # type: List[InstallRequirement]

        def add_req(subreq, extras_requested):
            sub_install_req = self._make_install_req(
                str(subreq),
                req_to_install,
            )
            parent_req_name = req_to_install.name
            to_scan_again, add_to_parent = requirement_set.add_requirement(
                sub_install_req,
                parent_req_name=parent_req_name,
                extras_requested=extras_requested,
            )
            if parent_req_name and add_to_parent:
                self._discovered_dependencies[parent_req_name].append(
                    add_to_parent
                )
            more_reqs.extend(to_scan_again)

        with indent_log():
            # We add req_to_install before its dependencies, so that we
            # can refer to it when adding dependencies.
            if not requirement_set.has_requirement(req_to_install.name):
                # 'unnamed' requirements will get added here
                # 'unnamed' requirements can only come from being directly
                # provided by the user.
                assert req_to_install.is_direct
                requirement_set.add_requirement(
                    req_to_install, parent_req_name=None,
                )

            if (not self.ignore_dependencies) and (not req_to_install.force_eager_download):
                if req_to_install.extras:
                    logger.debug(
                        "Installing extra requirements: %r",
                        ','.join(req_to_install.extras),
                    )
                missing_requested = sorted(
                    set(req_to_install.extras) - set(dist.extras)
                )
                for missing in missing_requested:
                    logger.warning(
                        '%s does not provide the extra \'%s\'',
                        dist, missing
                    )

                available_requested = sorted(
                    set(dist.extras) & set(req_to_install.extras)
                )
                for subreq in dist.requires(available_requested):
                    add_req(subreq, extras_requested=available_requested)

            if not req_to_install.editable and not req_to_install.satisfied_by:
                # XXX: --no-install leads this to report 'Successfully
                # downloaded' for only non-editable reqs, even though we took
                # action on them.
                requirement_set.successfully_downloaded.append(req_to_install)

        return more_reqs

    def get_installation_order(self, req_set):
        # type: (RequirementSet) -> List[InstallRequirement]
        """Create the installation order.

        The installation order is topological - requirements are installed
        before the requiring thing. We break cycles at an arbitrary point,
        and make no other guarantees.
        """
        # The current implementation, which we may change at any point
        # installs the user specified things in the order given, except when
        # dependencies must come earlier to achieve topological order.
        order = []
        ordered_reqs = set()  # type: Set[InstallRequirement]

        def schedule(req):
            if req.satisfied_by or req in ordered_reqs:
                return
            if req.constraint:
                return
            ordered_reqs.add(req)
            for dep in self._discovered_dependencies[req.name]:
                schedule(dep)
            order.append(req)

        for install_req in req_set.requirements.values():
            schedule(install_req)
        return order
