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

import json
import logging
import os
import re
import struct
import sys
import zlib
from collections import defaultdict
from itertools import chain

from pip._vendor.packaging import specifiers
from pip._vendor.packaging.requirements import Requirement
from pip._vendor.requests.exceptions import MissingSchema

from pip._internal.distributions.base import AbstractDistribution
from pip._internal.exceptions import (
    BestVersionAlreadyInstalled,
    DistributionNotFound,
    HashError,
    HashErrors,
    UnsupportedPythonVersion,
    UnsupportedWheel,
)
from pip._internal.models.link import Link
from pip._internal.req.req_install import InstallRequirement
from pip._internal.resolution.base import BaseResolver
from pip._internal.utils.compatibility_tags import get_supported
from pip._internal.req.req_set import RequirementSet
from pip._internal.utils.logging import indent_log
from pip._internal.utils.misc import dist_in_usersite, normalize_version_info
from pip._internal.utils.packaging import (
    check_requires_python,
    get_requires_python,
)
from pip._internal.utils.typing import MYPY_CHECK_RUNNING
from pip._internal.utils.urls import get_url_scheme

try:
    from json import JSONDecodeError
except ImportError:
    # PY2
    JSONDecodeError = ValueError  # type: ignore

if MYPY_CHECK_RUNNING:
    from typing import Callable, DefaultDict, Dict, List, Optional, Set, Tuple
    from pip._vendor import pkg_resources

    from pip._internal.cache import WheelCache
    from pip._internal.distributions import AbstractDistribution
    from pip._internal.index.package_finder import PackageFinder
    from pip._internal.models.link import Link
    from pip._internal.network.session import PipSession
    from pip._internal.operations.prepare import RequirementPreparer
    from pip._internal.req.req_install import InstallRequirement
    from pip._internal.resolution.base import InstallRequirementProvider

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
    def __init__(self, preparer, req):
        super(LazyDistribution, self).__init__(req)
        self._preparer = preparer
        self._real_dist = None

    def _maybe_fetch_underlying_dist(self):
        if not self._real_dist:
            self._real_dist = self._preparer.prepare_linked_requirement(
                self.req)
        return self._real_dist

    def has_been_downloaded(self):
        return self._real_dist is not None

    def get_pkg_resources_distribution(self):
        return (self._maybe_fetch_underlying_dist()
                .get_pkg_resources_distribution())

    def prepare_distribution_metadata(self, finder, build_isolation):
        return (self._maybe_fetch_underlying_dist()
                .prepare_distribution_metadata(finder, build_isolation))


# From https://stackoverflow.com/a/1089787/2518889:
def _inflate(data):
    decompress = zlib.decompressobj(-zlib.MAX_WBITS)
    inflated = decompress.decompress(data)
    inflated += decompress.flush()
    return inflated


def _decode_4_byte_unsigned(byte_string):
    """Unpack as a little-endian unsigned long."""
    assert isinstance(byte_string, bytes) and len(byte_string) == 4
    return struct.unpack('<L', byte_string)[0]


def _decode_2_byte_unsigned(byte_string):
    """Unpack as a little-endian unsigned short."""
    assert isinstance(byte_string, bytes) and len(byte_string) == 2
    return struct.unpack('<H', byte_string)[0]


class PersistentRequirementDependencyCache(object):
    def __init__(self, file_path):
        # type: (str) -> None
        self._file_path = file_path
        self._cache = None      # type: Optional[RequirementDependencyCache]

    def __enter__(self):
        # type: () -> RequirementDependencyCache
        # Ensure the parent directory of the cache file is created.
        parent = os.path.dirname(self._file_path)
        if not os.path.isdir(parent):
            os.makedirs(parent)

        try:
            with open(self._file_path, 'rb') as f:
                cache_from_config = RequirementDependencyCache.deserialize(
                    f.read())
        except (IOError, OSError, JSONDecodeError, EOFError) as e:
            # If the file does not exist, or the cache was not readable for any
            # reason, just start anew.
            logger.debug('error reading dependency cache: {}.'.format(e))
            cache_from_config = RequirementDependencyCache({})

        self._cache = cache_from_config
        return self._cache

    def __exit__(self, exc_type, exc_value, exc_tb):
        try:
            parent_dir = os.path.dirname(self._file_path)
            if not os.path.exists(parent_dir):
                os.makedirs(parent_dir)
            with open(self._file_path, 'wb') as f:
                f.write(self._cache.serialize())
        finally:
            self._cache = None


class RequirementConcreteUrl(object):
    @classmethod
    def from_install_req(cls, install_req):
        # type: (InstallRequirement) -> RequirementConcreteUrl
        return cls(install_req.req, install_req.link.url)

    def into_install_req(self, comes_from):
        # type: (Optional[InstallRequirement]) -> InstallRequirement
        return InstallRequirement(
            req=self.req,
            comes_from=comes_from,
            link=Link(self.url),
        )

    def __init__(self, req, url):
        # type: (Requirement, str) -> None
        self.req = req
        self.url = url

    def __hash__(self):
        # type: () -> int
        return hash((str(self.req), self.url))

    def __eq__(self, other):
        # type: (object) -> bool
        return (isinstance(other, type(self)) and
                str(self.req) == str(other.req) and self.url == other.url)

    def __repr__(self):
        # type: () -> str
        return '{}({!r}, {!r})'.format(type(self).__name__, self.req, self.url)

    record_separator = '|'

    def into_json(self):
        # type: () -> str
        return self.record_separator.join([
            str(self.req),
            self.url
        ])

    @classmethod
    def from_json(cls, comma_delimited):
        # type: (str) -> RequirementConcreteUrl
        req, url = tuple(comma_delimited.split(cls.record_separator))
        return cls(Requirement(req), url)


if MYPY_CHECK_RUNNING:
    RequirementsCacheDict = \
        Dict[RequirementConcreteUrl, List[RequirementConcreteUrl]]


class RequirementDependencyCache(object):
    def __init__(self, cache_from_config):
        # type: (RequirementsCacheDict) -> None
        self._cache = cache_from_config

    def add_dependency_links(self, req, dep_reqs):
        # type: (InstallRequirement, List[InstallRequirement]) -> None
        base_concrete_req = RequirementConcreteUrl.from_install_req(req)
        dep_concrete_reqs = [
            RequirementConcreteUrl.from_install_req(dep)
            for dep in dep_reqs
        ]

        prev_deps = self._cache.get(base_concrete_req, None)

        if prev_deps is not None and dep_concrete_reqs != prev_deps:
            logger.debug('prev_deps {prev_deps} were not equal to {dep_concrete_reqs}'
                         .format(prev_deps=prev_deps,
                                 dep_concrete_reqs=dep_concrete_reqs))
        self._cache[base_concrete_req] = dep_concrete_reqs

    def get(self,
            concrete_url,       # type: RequirementConcreteUrl
            ):
        # type: (...) -> Optional[List[RequirementConcreteUrl]]
        return self._cache.get(concrete_url, None)

    def serialize(self):
        # type: () -> bytes
        return json.dumps({
            url.into_json(): [dep_url.into_json() for dep_url in deps]
            for url, deps in self._cache.items()
        }).encode('utf-8')

    @classmethod
    def deserialize(cls, json_object):
        # type: (bytes) -> RequirementDependencyCache
        return cls({
            RequirementConcreteUrl.from_json(url): [
                RequirementConcreteUrl.from_json(dep_url)
                for dep_url in deps
            ]
            for url, deps in json.loads(json_object).items()
        })


class Resolver(BaseResolver):
    """Resolves which packages need to be installed/uninstalled to perform \
    the requested operation without breaking the requirements of any package.
    """

    _allowed_strategies = {"eager", "only-if-needed", "to-satisfy-only"}

    def __init__(
        self,
        preparer,  # type: RequirementPreparer
        finder,  # type: PackageFinder
        wheel_cache,  # type: Optional[WheelCache]
        make_install_req,  # type: InstallRequirementProvider
        use_user_site,  # type: bool
        ignore_dependencies,  # type: bool
        ignore_installed,  # type: bool
        ignore_requires_python,  # type: bool
        force_reinstall,  # type: bool
        upgrade_strategy,  # type: str
        py_version_info=None,  # type: Optional[Tuple[int, ...]]
        quickly_parse_sub_requirements=False,  # type: bool
        session=None,                         # type: PipSession
        persistent_dependency_cache=None,
        # type: PersistentRequirementDependencyCache
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
        self.wheel_cache = wheel_cache

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
        self.session = session

        self._persistent_dependency_cache = persistent_dependency_cache

    def resolve(self, root_reqs, check_supported_wheels):
        # type: (List[InstallRequirement], bool) -> RequirementSet
        """Resolve what operations need to be done

        As a side-effect of this method, the packages (and their dependencies)
        are downloaded, unpacked and prepared for installation. This
        preparation is done by ``pip.operations.prepare``.

        Once PyPI has static dependency metadata available, it would be
        possible to move the preparation to become a step separated from
        dependency resolution.
        """
        with self._persistent_dependency_cache as dep_cache:

            requirement_set = RequirementSet(
                check_supported_wheels=check_supported_wheels
            )
            for req in root_reqs:
                requirement_set.add_requirement(req)

            # Actually prepare the files, and collect any exceptions. Most hash
            # exceptions cannot be checked ahead of time, because
            # req.populate_link() needs to be called before we can make
            # decisions based on link type.
            discovered_reqs = []  # type: List[InstallRequirement]
            forced_eager_reqs = []  # type: List[InstallRequirement]
            hash_errors = HashErrors()

            found_reqs = set()  # type: Set[str]

            for req in chain(root_reqs, discovered_reqs, forced_eager_reqs):

                if (req.force_eager_download and
                        self.quickly_parse_sub_requirements):
                    continue

                if req.name in found_reqs:
                    continue
                found_reqs.add(req.name)

                try:
                    dep_reqs = [
                        r for r in
                        self._resolve_one(requirement_set, req, dep_cache)
                        if r.match_markers()
                    ]

                    link_populated_dep_reqs = [
                        (dep
                         if dep.link
                         else self._get_abstract_dist_for(dep).req)
                        for dep in dep_reqs
                    ]

                    cur_discovered_reqs = []

                    for r in link_populated_dep_reqs:
                        if r.force_eager_download:
                            forced_eager_reqs.append(r)
                        else:
                            cur_discovered_reqs.append(r)

                    dep_cache.add_dependency_links(req, cur_discovered_reqs)

                    discovered_reqs.extend(cur_discovered_reqs)
                except HashError as exc:
                    exc.req = req
                    hash_errors.append(exc)

            if hash_errors:
                raise hash_errors

            return requirement_set

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

    def _find_requirement_link(self, req):
        # type: (InstallRequirement) -> Optional[Link]
        upgrade = self._is_upgrade_allowed(req)
        best_candidate = self.finder.find_requirement(req, upgrade)
        if not best_candidate:
            return None

        # Log a warning per PEP 592 if necessary before returning.
        link = best_candidate.link
        if link.is_yanked:
            reason = link.yanked_reason or '<none given>'
            msg = (
                # Mark this as a unicode string to prevent
                # "UnicodeEncodeError: 'ascii' codec can't encode character"
                # in Python 2 when the reason contains non-ascii characters.
                u'The candidate selected for download or install is a '
                'yanked version: {candidate}\n'
                'Reason for being yanked: {reason}'
            ).format(candidate=best_candidate, reason=reason)
            logger.warning(msg)

        return link

    def _populate_link(self, req):
        # type: (InstallRequirement) -> None
        """Ensure that if a link can be found for this, that it is found.

        Note that req.link may still be None - if the requirement is already
        installed and not needed to be upgraded based on the return value of
        _is_upgrade_allowed().

        If preparer.require_hashes is True, don't use the wheel cache, because
        cached wheels, always built locally, have different hashes than the
        files downloaded from the index server and thus throw false hash
        mismatches. Furthermore, cached wheels at present have undeterministic
        contents due to file modification times.
        """
        if req.link is None:
            req.link = self._find_requirement_link(req)

        if self.wheel_cache is None or self.preparer.require_hashes:
            return
        cache_entry = self.wheel_cache.get_cache_entry(
            link=req.link,
            package_name=req.name,
            supported_tags=get_supported(),
        )
        if cache_entry is not None:
            logger.debug('Using cached wheel link: %s', cache_entry.link)
            if req.link is req.original_link and cache_entry.persistent:
                req.original_link_is_in_wheel_cache = True
            req.link = cache_entry.link

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

        # We eagerly populate the link, since that's our "legacy" behavior.
        require_hashes = self.preparer.require_hashes
        self._populate_link(req)

        # If we've been configured to hack out the METADATA file from a remote
        # wheel, extract sub requirements first!
        if (self.quickly_parse_sub_requirements and
                (not req.force_eager_download) and
                req.link.is_wheel):
            return LazyDistribution(self.preparer, req)

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
        """Obtain the dependencies of a wheel requirement by scanning the
        METADATA file."""
        url = str(req.link)
        scheme = get_url_scheme(url)
        assert scheme in ['http', 'https'], 'scheme was: {}, url was: {}, req was: {}'.format(scheme, url, req)

        head_resp = self.session.head(url)
        head_resp.raise_for_status()
        assert 'bytes' in head_resp.headers['Accept-Ranges']
        wheel_content_length = int(head_resp.headers['Content-Length'])

        _INITIAL_ENDING_BYTES_RANGE = max(2000, int(wheel_content_length * 0.01))

        shallow_begin = max((wheel_content_length - _INITIAL_ENDING_BYTES_RANGE),
                            0)
        wheel_shallow_resp = self.session.get(url, headers={
            'Range': ('bytes={shallow_begin}-{wheel_content_length}'
                      .format(shallow_begin=shallow_begin,
                              wheel_content_length=wheel_content_length)),
        })
        wheel_shallow_resp.raise_for_status()
        if wheel_content_length <= _INITIAL_ENDING_BYTES_RANGE:
            last_2k_bytes = wheel_shallow_resp.content
        else:
            assert len(wheel_shallow_resp.content) >= _INITIAL_ENDING_BYTES_RANGE
            last_2k_bytes = wheel_shallow_resp.content[-_INITIAL_ENDING_BYTES_RANGE:]

        sanitized_requirement_name = req.name.lower().replace('-', '_')
        metadata_file_pattern = (
            '{sanitized_requirement_name}[^/]+?.dist-info/METADATAPK'
            .format(sanitized_requirement_name=sanitized_requirement_name)
            .encode())
        filename_in_central_dir_header = re.search(metadata_file_pattern,
                                                   last_2k_bytes,
                                                   flags=re.IGNORECASE)

        try:
            _st = filename_in_central_dir_header.start()
        except AttributeError:
            raise Exception(
                'req: {}, pat: {}, len(b):{}, bytes:\n{}'
                .format(req, metadata_file_pattern, len(last_2k_bytes), last_2k_bytes))

        encoded_offset_for_local_file = last_2k_bytes[(_st - 4):_st]
        _off = _decode_4_byte_unsigned(encoded_offset_for_local_file)

        local_file_header_resp = self.session.get(url, headers={
            'Range': ('bytes={beg}-{end}'.format(beg=(_off + 18),
                                                 end=(_off + 30))),
        })
        local_file_header_resp.raise_for_status()

        if len(local_file_header_resp.content) == 13:
            file_header_no_filename = local_file_header_resp.content[:12]
        elif len(local_file_header_resp.content) > 12:
            file_header_no_filename = (
                local_file_header_resp.content[(_off + 18):(_off + 30)])
        else:
            file_header_no_filename = local_file_header_resp.content

        try:
            compressed_size = _decode_4_byte_unsigned(
                file_header_no_filename[:4])
        except AssertionError:
            raise Exception(
                'c: {}, _off: {}'
                .format(local_file_header_resp.content, _off)
            )
        uncompressed_size = _decode_4_byte_unsigned(
            file_header_no_filename[4:8])
        file_name_length = _decode_2_byte_unsigned(
            file_header_no_filename[8:10])
        assert file_name_length == (
            len(filename_in_central_dir_header.group(0)) - 2)
        extra_field_length = _decode_2_byte_unsigned(
            file_header_no_filename[10:12])
        compressed_start = _off + 30 + file_name_length + extra_field_length
        compressed_end = compressed_start + compressed_size

        metadata_file_resp = self.session.get(url, headers={
            'Range': ('bytes={compressed_start}-{compressed_end}'
                      .format(compressed_start=compressed_start,
                              compressed_end=compressed_end)),
        })
        metadata_file_resp.raise_for_status()

        header_response_length = len(local_file_header_resp.content)
        metadata_response_length = len(metadata_file_resp.content)
        if metadata_response_length == header_response_length:
            metadata_file_bytes = (
                metadata_file_resp.content[compressed_start:compressed_end])
        else:
            metadata_file_bytes = metadata_file_resp.content[:compressed_size]
        uncompressed_file_contents = _inflate(metadata_file_bytes)
        assert len(uncompressed_file_contents) == uncompressed_size

        decoded_metadata_file = uncompressed_file_contents.decode('utf-8')
        all_requirements = [
            Requirement(re.sub(r'^(.*) \((.*)\)$', r'\1\2', g[1]))
            for g in re.finditer(r'^Requires-Dist: (.*)$',
                                 decoded_metadata_file,
                                 flags=re.MULTILINE)
        ]
        return [
            InstallRequirement(
                req=r,
                comes_from=req,
            ) for r in all_requirements
        ]

    def _resolve_one(
        self,
        requirement_set,    # type: RequirementSet
        req_to_install,     # type: InstallRequirement
        dep_cache,          # type: RequirementDependencyCache
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

        with indent_log():
            # We add req_to_install before its dependencies, so that we
            # can refer to it when adding dependencies.
            if not requirement_set.has_requirement(req_to_install.name or ''):
                # 'unnamed' requirements will get added here
                # 'unnamed' requirements can only come from being directly
                # provided by the user.
                if not req_to_install.is_direct:
                    logger.debug("req should be direct, but isn't: {}"
                                 .format(req_to_install))
                    req_to_install.is_direct = True
                requirement_set.add_requirement(
                    req_to_install, parent_req_name=None,
                )

        if req_to_install.link and not req_to_install.force_eager_download:
            parent_req = req_to_install.copy()

            maybe_cached_sub_reqs = dep_cache.get(
                RequirementConcreteUrl.from_install_req(parent_req))
            if maybe_cached_sub_reqs is not None:
                logger.debug(
                    'cached sub requirements were found: {} for {}'
                    .format(maybe_cached_sub_reqs, parent_req.link))
                hydrated_sub_reqs = [
                    req.into_install_req(comes_from=parent_req)
                    for req in maybe_cached_sub_reqs
                ]

                parent_req.force_eager_download = True
                parent_req.is_direct = True

                # more_reqs = hydrated_sub_reqs + [parent_req]
                return hydrated_sub_reqs + [parent_req]

        abstract_dist = self._get_abstract_dist_for(req_to_install)

        assert abstract_dist.req.link is not None

        more_reqs = []  # type: List[InstallRequirement]

        cur_url = str(abstract_dist.req.link)
        cur_scheme = get_url_scheme(cur_url)
        is_remote = ((not abstract_dist.has_been_downloaded()) and
                     (cur_scheme in ['http', 'https']))
        is_wheel = abstract_dist.req.link.is_wheel

        # FIXME: perform the Requires-Python checking for shallowly-resolved
        # requirements (via self._hacky_extract_sub_reqs)!!!
        if is_remote and is_wheel:
            parent_req = abstract_dist.req.copy()

            maybe_cached_sub_reqs = dep_cache.get(
                RequirementConcreteUrl.from_install_req(parent_req))
            if maybe_cached_sub_reqs is not None:
                logger.debug(
                    'cached sub requirements were found: {} for {}'
                    .format(maybe_cached_sub_reqs, parent_req.link))
                hydrated_sub_reqs = [
                    req.into_install_req(comes_from=parent_req)
                    for req in maybe_cached_sub_reqs
                ]
            else:
                hydrated_sub_reqs = self._hacky_extract_sub_reqs(
                    parent_req)

            parent_req.force_eager_download = True
            parent_req.is_direct = True

            more_reqs = hydrated_sub_reqs + [parent_req]

        else:
            abstract_dist.req.has_backing_dist = True

            # Parse and return dependencies
            try:
                dist = abstract_dist.get_pkg_resources_distribution()
            except (UnsupportedWheel, MissingSchema):
                return []
            # This will raise UnsupportedPythonVersion if the given Python
            # version isn't compatible with the distribution's Requires-Python.
            _check_dist_requires_python(
                dist, version_info=self._py_version_info,
                ignore_requires_python=self.ignore_requires_python,
            )

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
                if ((not self.ignore_dependencies) and
                        (not req_to_install.force_eager_download)):
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

        with indent_log():
            if not req_to_install.editable and not req_to_install.satisfied_by:
                # XXX: --no-install leads this to report 'Successfully
                # downloaded' for only non-editable reqs, even though we took
                # action on them.
                req_to_install.successfully_downloaded = True

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
