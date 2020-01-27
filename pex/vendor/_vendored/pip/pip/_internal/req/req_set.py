# The following comment should be removed at some point in the future.
# mypy: strict-optional=False

from __future__ import absolute_import

import logging
from collections import OrderedDict

from pip._vendor.packaging import specifiers, version
from pip._vendor.packaging.utils import canonicalize_name

from pip._internal import pep425tags
from pip._internal.exceptions import InstallationError
from pip._internal.models.wheel import Wheel
from pip._internal.utils.logging import indent_log
from pip._internal.utils.typing import MYPY_CHECK_RUNNING

if MYPY_CHECK_RUNNING:
    from typing import Dict, Iterable, List, Optional, Tuple
    from pip._internal.req.req_install import InstallRequirement


logger = logging.getLogger(__name__)


class VersionConflictError(Exception):
    def __init__(self, conflicting_versions):
        super().__init__(f'conflicting versions were: {conflicting_versions}')
        self.conflicting_versions = conflicting_versions


class EqualsMismatchException(VersionConflictError):
    pass


class InvalidEqualityAndInequality(VersionConflictError):
    pass


class InvalidLeftRightBounds(VersionConflictError):
    pass


class RequirementSet(object):

    def rank(self):
        root_reqs = self.as_root_reqs()

        link_score = len(list(r for r in root_reqs if r.link))
        wheel_score = len(list(r for r in root_reqs if r.link and r.link.is_wheel))
        backing_dist_score = len(list(r for r in root_reqs if r.has_backing_dist))

        parents_score = len(self.parents)

        total = link_score + wheel_score + backing_dist_score + parents_score
        # NB: We only have increasing scores, but queue.PriorityQueue takes the lowest priority, not
        # highest! If the scores don't get too high, we can safely just subtract from some large
        # number.
        assert 300 > (total + 100)
        return 300 - total

    def resolve_has_been_completed(self):
        # type: () -> bool
        return all(r.has_backing_dist for r in self.as_root_reqs())

    @staticmethod
    def _minimize_versions(op, versions):
        first, rest = versions[0], versions[1:]
        for v in rest:
          if op in ['<', '<=']:
              if v < first:
                  first = v
          elif op in ['>', '>=']:
              if v > first:
                  first = v
          else:
              assert op == '=='
              if v !=  first:
                  raise EqualsMismatchException(versions)
        return first

    @staticmethod
    def _find_representative_specifier_set(op_pairs):
        equals_bound = op_pairs.get('==', None)

        right_bound = None
        right_op = None
        lt_ver = op_pairs.get('<', None)
        if lt_ver:
            if equals_bound and lt_ver >= equals_bound:
                raise InvalidEqualityAndInequality(list(op_pairs.items()))
            right_bound = lt_ver
            right_op = '<'
        lte_ver = op_pairs.get('<=', None)
        if lte_ver:
            if equals_bound and lte_ver > equals_bound:
                raise InvalidEqualityAndInequality(list(op_pairs.items()))
            if right_bound and lte_ver < right_bound:
                right_bound = lte_ver
                right_op = '<='

        left_bound = None
        left_op = None
        gt_ver = op_pairs.get('>', None)
        if gt_ver:
            if equals_bound and gt_ver <= equals_bound:
                raise InvalidEqualityAndInequality(list(op_pairs.items()))
            left_bound = gt_ver
            left_op = '>'
        gte_ver = op_pairs.get('>=', None)
        if gte_ver:
            if equals_bound and gte_ver < equals_bound:
                raise InvalidEqualityAndInequality(list(op_pairs.items()))
            if left_bound and gte_ver > left_bound:
                left_bound = gte_ver
                left_op = '>='

        if (right_op == '<=') and (left_op == '>='):
            if right_bound == left_bound:
                equals_bound = right_bound
        if equals_bound:
            return specifiers.SpecifierSet(f'=={equals_bound}')
        if right_bound and left_bound and (right_bound < left_bound):
            raise InvalidLeftRightBounds(list(op_pairs.items()))

        specifiers = [
            *([specifiers.Specifier(f'{left_op}{left_bound}')] if left_op else []),
            *([specifiers.Specifier(f'{right_op}{right_bound}')] if right_op else []),
        ]
        return specifiers.SpecifierSet(specifiers)

    @classmethod
    def _normalize_specifier_set(cls, specifier_set):
        by_dominating_operator = defaultdict(list)
        for specifier in specifier_set:
            by_dominating_operator[specifier.operator].append(version.parse(specifier.version))
        minimized_version_op_pairs = {
            op: cls._minimize_versions(op, versions)
            for op, versions in by_dominating_operator.items()
        }
        return cls._find_representative_specifier_set(minimized_version_op_pairs)

    def copy(self):
        # type: () -> RequirementSet
        ret = RequirementSet(require_hashes=self.require_hashes,
                             check_supported_wheels=self.check_supported_wheels)
        ret.requirements = self.requirements.copy()
        ret.unnamed_requirements = self.unnamed_requirements.copy()
        ret.successfully_downloaded = self.successfully_downloaded.copy()
        ret.reqs_to_cleanup = self.reqs_to_cleanup.copy()
        ret.parents = self.parents.copy() + [self]
        return ret

    def __init__(self, require_hashes=False, check_supported_wheels=True):
        # type: (bool, bool) -> None
        """Create a RequirementSet.
        """

        self.requirements = OrderedDict()  # type: Dict[str, InstallRequirement]  # noqa: E501
        self.check_supported_wheels = check_supported_wheels

        self.unnamed_requirements = []  # type: List[InstallRequirement]
        self.successfully_downloaded = []  # type: List[InstallRequirement]
        self.reqs_to_cleanup = []  # type: List[InstallRequirement]

        self.parents = []       # type: List[RequirementSet]

    def __str__(self):
        # type: () -> str
        requirements = sorted(
            (req for req in self.requirements.values() if not req.comes_from),
            key=lambda req: canonicalize_name(req.name),
        )
        return ' '.join(str(req.req) for req in requirements)

    def __repr__(self):
        # type: () -> str
        requirements = sorted(
            self.requirements.values(),
            key=lambda req: canonicalize_name(req.name),
        )

        format_string = '<{classname} object; {count} requirement(s): {reqs}>'
        return format_string.format(
            classname=self.__class__.__name__,
            count=len(requirements),
            reqs=', '.join(str(req.req) for req in requirements),
        )

    def add_unnamed_requirement(self, install_req):
        # type: (InstallRequirement) -> None
        assert not install_req.name
        self.unnamed_requirements.append(install_req)

    def add_named_requirement(self, install_req):
        # type: (InstallRequirement) -> None
        assert install_req.name

        project_name = canonicalize_name(install_req.name)
        self.requirements[project_name] = install_req

    def as_root_reqs(self):
        return self.unnamed_requirements + list(self.requirements.values())

    def add_requirement(
        self,
        install_req,  # type: InstallRequirement
        parent_req_name=None,  # type: Optional[str]
        extras_requested=None  # type: Optional[Iterable[str]]
    ):
        # type: (...) -> Tuple[List[InstallRequirement], Optional[InstallRequirement]]  # noqa: E501
        """Add install_req as a requirement to install.

        :param parent_req_name: The name of the requirement that needed this
            added. The name is used because when multiple unnamed requirements
            resolve to the same name, we could otherwise end up with dependency
            links that point outside the Requirements set. parent_req must
            already be added. Note that None implies that this is a user
            supplied requirement, vs an inferred one.
        :param extras_requested: an iterable of extras used to evaluate the
            environment markers.
        :return: Additional requirements to scan. That is either [] if
            the requirement is not applicable, or [install_req] if the
            requirement is applicable and has just been added.
        """
        # If the markers do not match, ignore this requirement.
        if not install_req.match_markers(extras_requested):
            logger.info(
                "Ignoring %s: markers '%s' don't match your environment",
                install_req.name, install_req.markers,
            )
            return [], None

        # If the wheel is not supported, raise an error.
        # Should check this after filtering out based on environment markers to
        # allow specifying different wheels based on the environment/OS, in a
        # single requirements file.
        if install_req.link and install_req.link.is_wheel:
            wheel = Wheel(install_req.link.filename)
            tags = pep425tags.get_supported()
            if (self.check_supported_wheels and not wheel.supported(tags)):
                raise InstallationError(
                    "%s is not a supported wheel on this platform." %
                    wheel.filename
                )

        # This next bit is really a sanity check.
        assert install_req.is_direct == (parent_req_name is None), (
            "a direct req shouldn't have a parent and also, "
            "a non direct req should have a parent"
        )

        # Unnamed requirements are scanned again and the requirement won't be
        # added as a dependency until after scanning.
        if not install_req.name:
            self.add_unnamed_requirement(install_req)
            return [install_req], None

        try:
            existing_req = self.get_requirement(install_req.name)
        except KeyError:
            existing_req = None

        # When no existing requirement exists, add the requirement as a
        # dependency and it will be scanned again after.
        if not existing_req:
            self.add_named_requirement(install_req)
            # We'd want to rescan this requirement later
            return [install_req], install_req

        try:
            normalized_specifier_set = self._normalize_specifier_set(
                existing_req.req.specifier & install_req.req.specifier)
        except VersionConflictError as e:
            raise InstallationError(
                "Version conflict error {e}: %s (already in %s, name=%r)"
                % (install_req, existing_req, install_req.name)
            ) from e

        # Assume there's no need to scan, and that we've already
        # encountered this for scanning.
        if (install_req.constraint or
            (not existing_req.constraint) or
            # If we've made no change to the accepted specifiers, we don't need to consider
            # re-scanning!
            (normalized_specifier_set == existing_req.req.specifier)):
            return [], existing_req
        existing_req.req.specifier = normalized_specifier_set

        does_not_satisfy_constraint = (
            install_req.link and
            not (
                existing_req.link and
                install_req.link.path == existing_req.link.path
            )
        )
        if does_not_satisfy_constraint:
            self.reqs_to_cleanup.append(install_req)
            raise InstallationError(
                "Could not satisfy constraints for '%s': "
                "installation from path or url cannot be "
                "constrained to a version" % install_req.name,
            )
        # If we're now installing a constraint, mark the existing
        # object for real installation.
        existing_req.constraint = False
        existing_req.extras = tuple(sorted(
            set(existing_req.extras) | set(install_req.extras)
        ))
        logger.debug(
            "Setting %s extras to: %s",
            existing_req, existing_req.extras,
        )

        # Return the existing requirement for addition to the parent and
        # scanning again.
        return [existing_req], existing_req

    def has_requirement(self, name):
        # type: (str) -> bool
        project_name = canonicalize_name(name)

        return (
            project_name in self.requirements and
            not self.requirements[project_name].constraint
        )

    def get_requirement(self, name):
        # type: (str) -> InstallRequirement
        project_name = canonicalize_name(name)

        if project_name in self.requirements:
            return self.requirements[project_name]

        raise KeyError("No project with the name %r" % name)

    def cleanup_files(self):
        # type: () -> None
        """Clean up files, remove builds."""
        logger.debug('Cleaning up...')
        with indent_log():
            for req in self.reqs_to_cleanup:
                req.remove_temporary_source()
