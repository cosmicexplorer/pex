"""Dependency Resolution

The dependency resolution in pip is performed as follows:

???
"""

# The following comment should be removed at some point in the future.
# mypy: strict-optional=False
# mypy: disallow-untyped-defs=False

import abc
import json
import logging
import re
import struct
import sys
import zlib
from collections import defaultdict

from pip._vendor.packaging.markers import Marker as PipMarker
from pip._vendor.packaging.requirements import Requirement as PipRequirement
from pip._vendor.packaging.specifiers import SpecifierSet as PipSpecifierSet
from pip._vendor.packaging.utils import canonicalize_name
from pip._vendor.packaging.version import Version as PipVersion
from pip._vendor.resolvelib import AbstractProvider, BaseReporter, Resolver
from pip._vendor.six import add_metaclass

from pip._internal.models.link import Link
from pip._internal.req.req_install import InstallRequirement
from pip._internal.resolution.legacy.resolver import (
    _check_dist_requires_python,
)
from pip._internal.utils.misc import normalize_version_info
from pip._internal.utils.models import KeyBasedCompareMixin
from pip._internal.utils.typing import MYPY_CHECK_RUNNING
from pip._internal.utils.urls import get_url_scheme

try:
    from json import JSONDecodeError
except ImportError:
    # PY2
    JSONDecodeError = ValueError  # type: ignore

if MYPY_CHECK_RUNNING:
    from typing import Any, Dict, List, Optional, Tuple

    from pip._internal.index.package_finder import PackageFinder
    from pip._internal.network.session import PipSession
    from pip._internal.operations.prepare import RequirementPreparer


logger = logging.getLogger(__name__)


# Protocols:
@add_metaclass(abc.ABCMeta)
class Serializable(object):
    @abc.abstractmethod
    def serialize(self):
        # type: () -> str
        pass

    @classmethod
    @abc.abstractmethod
    def deserialize(cls, s):
        # type: (str) -> Serializable
        pass


# Analogies for all the terms from the resolvelib README.rst:
class Package(Serializable):
    """A thing that can be installed. A Package can have one or more versions
    available for installation."""
    def __init__(self, name, extras=None):
        # type: (str, Optional[List[str]]) -> None
        self.name = canonicalize_name(name)
        self.extras = tuple(
            s for s in sorted(extras or [])
            if s != ''
        )

    def __hash__(self):
        # type: () -> int
        return hash((self.name, self.extras))

    def __eq__(self, other):
        # type: (object) -> bool
        return (isinstance(other, type(self)) and
                self.name == other.name and
                self.extras == other.extras)

    record_separator = '|'

    def serialize(self):
        # type: () -> str
        return self.record_separator.join([
            self.name,
            ','.join(self.extras),
        ])

    @classmethod
    def deserialize(cls, s):
        name, _, joined_extras = tuple(s.partition(cls.record_separator))
        extras = joined_extras.split(',')
        return cls(name, extras=extras)

    def decorative_name_with_extras(self):
        # type: () -> str
        ret = self.name
        if self.extras:
            ret = '{}[{}]'.format(ret, ','.join(self.extras))
        return ret

    def __repr__(self):
        # type: () -> str
        return 'Package({!r}, {!r})'.format(self.name, self.extras)


class Version(Serializable):
    """A string, usually in a number form, describing a snapshot of a
    Package. This number should increase when a Package posts a new snapshot,
    i.e. a higher number means a more up-to-date snapshot."""

    def __init__(self, inner):
        # type: (PipVersion) -> None
        self.inner = inner

    def __hash__(self):
        # type: () -> int
        return hash(self.inner)

    def __eq__(self, other):
        # type: (object) -> bool
        return isinstance(other, type(self)) and self.inner == other.inner

    def serialize(self):
        # type: () -> str
        return str(self.inner)

    @classmethod
    def deserialize(cls, s):
        return cls(PipVersion(s))

    def __repr__(self):
        # type: () -> str
        return 'Version({!r})'.format(self.inner)


class Specifier(Serializable):
    """A collection of one or more Versions. This could be a wildcard,
    indicating that any Version is acceptable."""

    def __init__(self, inner):
        # type: (PipSpecifierSet) -> None
        self.inner = inner

    def __hash__(self):
        # type: () -> int
        return hash(self.inner)

    def __eq__(self, other):
        # type: (object) -> bool
        return isinstance(other, type(self)) and self.inner == other.inner

    def serialize(self):
        return str(self.inner)

    @classmethod
    def deserialize(cls, s):
        return cls(PipSpecifierSet(s))

    def __repr__(self):
        # type: () -> str
        return 'Specifier({!r})'.format(self.inner)


@add_metaclass(abc.ABCMeta)
class Dependency(object):
    """A dependency can be either a requirement, or a candidate. In
    implementations you can treat it as the parent class and/or a protocol of
    the two."""

    @abc.abstractproperty
    def package(self):
        # type: () -> Package
        pass


class Candidate(Dependency, Serializable):
    """A combination of a Package and a Version, i.e. a "concrete
    requirement". Python people sometimes call this a "locked" or "pinned"
    dependency. Both of "requirement" and "dependency", however, SHOULD NOT be
    used when describing a Candidate, to avoid confusion.

    Some resolver architectures (e.g. Molinillo) refer this as a
    "specicifation", but this is not chosen to avoid confusion with a
    *Specifier*."""

    class InvalidPackageUrlError(Exception):
        pass

    @classmethod
    def from_package_and_link(cls, package, link, finder):
        # type: (Package, Link, PackageFinder) -> Candidate
        link_evaluator = finder.make_link_evaluator(package.name)
        is_candidate, result = link_evaluator.evaluate_link(link)
        if not is_candidate:
            raise cls.InvalidPackageUrlError(result)

        version = PipVersion(result)

        return cls(package, Version(version), link)

    def __init__(self, package, version, link):
        # type: (Package, Version, Link) -> None
        self._package = package
        self.version = version
        self.link = link

    @property
    def package(self):
        return self._package

    def __hash__(self):
        # type: () -> int
        return hash((self.package, self.version, self.link))

    def __eq__(self, other):
        # type: (object) -> bool
        return (isinstance(other, type(self)) and
                self.package == other.package and
                self.version == other.version and
                self.link == other.link)

    record_separator = '$'

    def serialize(self):
        # type: () -> str
        return self.record_separator.join([
            self.package.serialize(),
            self.version.serialize(),
            self.link.url,
        ])

    @classmethod
    def deserialize(cls, s):
        package, version, url = tuple(s.split(cls.record_separator))
        return cls(
            Package.deserialize(package),
            Version.deserialize(version),
            Link(url),
        )

    def into_install_req(self):
        # type: () -> InstallRequirement
        return InstallRequirement(
            req=PipRequirement('{}=={}'.format(
                self.package.decorative_name_with_extras(),
                self.version.serialize(),
            )),
            comes_from=None,
            link=self.link,
        )

    def __repr__(self):
        # type: () -> str
        return 'Candidate({!r}, {!r}, {!r})'.format(
            self.package, self.version, self.link)


class Requirement(Serializable):
    """An intention to acquire a needed package, i.e. an "abstract
    requirement". A "dependency", if not clarified otherwise, also refers to
    this concept.

    A Requirement should specify two things: a Package, and a Specifier.  """

    @classmethod
    def from_pip_requirement(cls, req):
        # type: (PipRequirement) -> Requirement
        return cls(package=Package(req.name, extras=list(req.extras)),
                   specifier=Specifier(req.specifier),
                   marker=req.marker)

    def __init__(self, package, specifier, marker):
        # type: (Package, Specifier, Optional[PipMarker]) -> None
        self._package = package
        self.specifier = specifier
        self._marker = marker

    def evaluate_marker(self, context):
        if not self._marker:
            return True
        return self._marker.evaluate(context)

    @property
    def package(self):
        return self._package

    def __hash_(self):
        # type: () -> int
        return hash((self.package, self.specifier, self._marker))

    def __eq__(self, other):
        # type: (object) -> bool
        return (isinstance(other, type(self)) and
                self.package == other.package and
                self.specifier == other.specifier and
                self._marker == other._marker)

    record_separator = '`'

    def serialize(self):
        return self.record_separator.join([
            self.package.serialize(),
            self.specifier.serialize(),
            (str(self._marker) if self._marker else ''),
        ])

    @classmethod
    def deserialize(cls, s):
        package, specifier, marker = tuple(s.split(cls.record_separator))
        return cls(
            Package.deserialize(package),
            Specifier.deserialize(specifier),
            PipMarker(marker) if marker else None,
        )

    def __repr__(self):
        # type: () -> str
        return 'Requirement({!r}, {!r}, {!r})'.format(
            self.package, self.specifier, self._marker)


class RequirementInformation(object):
    """Each pair is a requirement contributing to this criterion, and the
    candidate that provides the requirement."""

    def __init__(self, requirement, parent):
        # type: (Requirement, Optional[Candidate]) -> None
        self.requirement = requirement
        self.parent = parent

    def is_direct(self):
        # type: () -> bool
        return self.parent is None

    @classmethod
    def from_tuple(cls,
                   tupled,      # type: Tuple[Requirement, Optional[Candidate]]
                   ):
        # type: (...) -> RequirementInformation
        req, parent = tupled
        return cls(req, parent)


class Preference(KeyBasedCompareMixin):
    """The preference is defined as "I think this requirement should be
    resolved first". The lower the return value is, the more preferred this
    group of arguments is."""

    def __init__(self, is_in_cache, is_wheel, num_possible_candidates):
        # type: (bool, bool, int) -> None
        self.is_in_cache = is_in_cache
        self.is_wheel = is_wheel
        self.num_possible_candidates = num_possible_candidates

        super(Preference, self).__init__(
            key=(
                not self.is_in_cache,
                not self.is_wheel,
                self.num_possible_candidates,
            ),
            defining_class=Preference,
        )

    def __repr__(self):
        # type: () -> str
        return 'Preference({!r}, {!r}, {!r})'.format(
            self.is_in_cache, self.is_wheel, self.num_possible_candidates)


# Implementations of framework types:
class PipProvider(AbstractProvider):
    """Resolves which packages need to be installed/uninstalled to perform \
    the requested operation without breaking the requirements of any package.
    """

    def __init__(self,
                 preparer,  # type: RequirementPreparer
                 finder,  # type: PackageFinder
                 ignore_requires_python,  # type: bool
                 py_version_info=None,  # type: Optional[Tuple[int, ...]]
                 session=None,                         # type: PipSession
                 dependency_cache=None,  # type: RequirementDependencyCache
                 ):
        # type: (...) -> None

        if py_version_info is None:
            py_version_info = sys.version_info[:3]
        else:
            py_version_info = normalize_version_info(py_version_info)

        self._py_version_info = py_version_info

        self.preparer = preparer
        self.finder = finder

        self.ignore_requires_python = ignore_requires_python

        self.session = session

        self._dependency_cache = dependency_cache

    @property
    def require_hashes(self):
        # type: () -> bool
        return self.preparer.require_hashes

    def identify(self, dependency):
        # type: (Dependency) -> Package
        return dependency.package

    def get_preference(
            self,
            resolution,         # type: Optional[Candidate]
            candidates,         # type: List[Candidate]
            information,        # type: List[Tuple[Requirement, Candidate]]
    ):
        # type: (...) -> Preference
        # FIXME: use this information!!!
        _req_infos = [
            RequirementInformation.from_tuple(inf) for inf in information
        ]

        is_in_cache = (bool(resolution) and
                       self._dependency_cache.has(resolution))
        is_wheel = bool(resolution) and resolution.link.is_wheel
        return Preference(
            is_in_cache=is_in_cache,
            is_wheel=is_wheel,
            num_possible_candidates=len(candidates))

    def find_matches(self, requirement):
        # type: (Requirement) -> List[Candidate]
        candidates = [
            Candidate.from_package_and_link(requirement.package, cand.link,
                                            self.finder)
            for cand in self.finder.find_all_candidates(
                requirement.package.name)
        ]
        by_version = defaultdict(lambda: defaultdict(list))

        for c in candidates:
            by_version[c.package][c.version].append(c.link)

        with_at_most_one_link = []
        for package, versionings in by_version.items():
            for version, all_such_links in versionings.items():
                for l in all_such_links:
                    cur_cand = Candidate(package, version, l)
                    # Prefer candidates that we have in the cache.
                    if self._dependency_cache.has(cur_cand):
                        with_at_most_one_link.append(cur_cand)
                        break
                    # Prefer wheels to sdists.
                    elif l.is_wheel:
                        with_at_most_one_link.append(cur_cand)
                        break
                else:
                    backup_cand = Candidate(package, version,
                                            all_such_links[0])
                    with_at_most_one_link.append(backup_cand)

        return with_at_most_one_link

    def is_satisfied_by(self, requirement, candidate):
        # type: (Requirement, Candidate) -> bool
        context = {'extra': candidate.package.extras}
        return ((candidate.version.inner in requirement.specifier.inner) and
                requirement.evaluate_marker(context))

    def _hacky_extract_sub_reqs(self, candidate):
        # type: (Candidate) -> List[Requirement]
        """Obtain the dependencies of a wheel requirement by scanning the
        METADATA file."""
        url = candidate.link.url
        scheme = get_url_scheme(url)
        assert scheme in ['http', 'https']

        head_resp = self.session.head(url)
        head_resp.raise_for_status()
        assert 'bytes' in head_resp.headers['Accept-Ranges']
        wheel_content_length = int(head_resp.headers['Content-Length'])

        shallow_begin = max(wheel_content_length - 2000, 0)
        wheel_shallow_resp = self.session.get(url, headers={
            'Range': ('bytes={shallow_begin}-{wheel_content_length}'
                      .format(shallow_begin=shallow_begin,
                              wheel_content_length=wheel_content_length)),
        })
        wheel_shallow_resp.raise_for_status()
        if wheel_content_length <= 2000:
            last_2k_bytes = wheel_shallow_resp.content
        else:
            assert len(wheel_shallow_resp.content) >= 2000
            last_2k_bytes = wheel_shallow_resp.content[-2000:]

        sanitized_requirement_name = (candidate.package.name
                                      .lower()
                                      .replace('-', '_'))
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
                'candidate: {}, pat: {!r}, len(b):{}'
                .format(candidate, metadata_file_pattern, len(last_2k_bytes)))

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
            PipRequirement(re.sub(r'^(.*) \((.*)\)$', r'\1\2', g[1]))
            for g in re.finditer(r'^Requires-Dist: (.*)$',
                                 decoded_metadata_file,
                                 flags=re.MULTILINE)
        ]
        return [Requirement.from_pip_requirement(r) for r in all_requirements]

    def _maybe_cached_dependencies(self, candidate):
        # type: (Candidate) -> List[Requirement]
        maybe_cached_deps = self._dependency_cache.get(candidate)
        if maybe_cached_deps is not None:
            return maybe_cached_deps

        if candidate.link.is_wheel:
            deps = self._hacky_extract_sub_reqs(candidate)
        else:
            req_install = candidate.into_install_req()
            abstract_dist = self.preparer.prepare_linked_requirement(
                req_install)
            dist = abstract_dist.get_pkg_resources_distribution()
            # This will raise UnsupportedPythonVersion if the given Python
            # version isn't compatible with the distribution's Requires-Python.
            _check_dist_requires_python(
                dist, version_info=self._py_version_info,
                ignore_requires_python=self.ignore_requires_python,
            )

            available_requested = sorted(
                set(dist.extras) & set(req_install.extras)
            )

            deps = [Requirement.from_pip_requirement(r)
                    for r in dist.requires(available_requested)]

        self._dependency_cache.add_dependency_links(candidate, deps)

        return deps

    def get_dependencies(self, candidate):
        # type: (Candidate) -> List[Requirement]
        deps = self._maybe_cached_dependencies(candidate)

        context = {'extra': candidate.package.extras}
        return [r for r in deps if r.evaluate_marker(context)]


class PipReporter(BaseReporter):

    def starting(self):
        # type: () -> None
        pass

    def starting_round(self, index):
        # type: (int) -> None
        pass

    def ending_round(self, index, state):
        # type: (int, Any) -> None
        pass

    def ending(self, state):
        # type: (Any) -> None
        pass


# Zip file hacking to download wheel METADATA without pulling down the whole
# file:

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


# Persistent dependency caching across pip invocations:
class PersistentRequirementDependencyCache(object):
    def __init__(self, file_path):
        # type: (str) -> None
        self._file_path = file_path
        self._cache = None      # type: Optional[RequirementDependencyCache]

    def __enter__(self):
        # type: () -> RequirementDependencyCache
        try:
            with open(self._file_path, 'r') as f:
                cache_from_config = RequirementDependencyCache.deserialize(
                    f.read())
        except (OSError, JSONDecodeError, EOFError) as e:
            # If the file does not exist, or the cache was not readable for any
            # reason, just start anew.
            logger.debug('error reading dependency cache: {}.'.format(e))
            cache_from_config = RequirementDependencyCache({})

        self._cache = cache_from_config
        return self._cache

    def __exit__(self, exc_type, exc_value, exc_tb):
        try:
            with open(self._file_path, 'w') as f:
                f.write(self._cache.serialize())
        finally:
            self._cache = None


if MYPY_CHECK_RUNNING:
    RequirementsCacheDict = Dict[Candidate, List[Requirement]]


class RequirementDependencyCache(Serializable):
    def __init__(self, cache_from_config):
        # type: (RequirementsCacheDict) -> None
        self._cache = cache_from_config

    def add_dependency_links(self, candidate, dependencies):
        # type: (Candidate, List[Requirement]) -> None
        prev_deps = self._cache.get(candidate, None)

        if prev_deps is not None:
            assert dependencies == prev_deps
        else:
            self._cache[candidate] = dependencies

    def has(self, candidate):
        # type: (Candidate) -> bool
        return candidate in self._cache

    def get(self, candidate):
        # type: (Candidate) -> Optional[List[Requirement]]
        return self._cache.get(candidate, None)

    def serialize(self):
        # type: () -> str
        return json.dumps({
            cand.serialize(): [dep_req.serialize() for dep_req in deps]
            for cand, deps in self._cache.items()
        })

    @classmethod
    def deserialize(cls, s):
        return cls({
            Candidate.deserialize(cand): [
                Requirement.deserialize(dep_req)
                for dep_req in deps
            ]
            for cand, deps in json.loads(s).items()
        })


class Result(object):
    def __init__(self, mapping):
        # type: (Dict[Package, Candidate]) -> None
        self.mapping = mapping


# Entry point to the resolve:
def resolve(provider, requirements):
    # type: (PipProvider, List[Requirement]) -> Result
    resolver = Resolver(provider, PipReporter())

    result = resolver.resolve(requirements)

    return Result(result.mapping)
