# The following comment should be removed at some point in the future.
# mypy: disallow-untyped-defs=False

from __future__ import absolute_import

import logging
import os
import sys

from pip._vendor.packaging.requirements import Requirement
from pip._vendor.packaging.utils import canonicalize_name
from pip._vendor.packaging.version import Version

from pip._internal.cli import cmdoptions
from pip._internal.cli.cmdoptions import make_target_python
from pip._internal.cli.req_command import (
    RequirementCommand,
    SessionCommandMixin,
    with_cleanup,
)
from pip._internal.models.link import Link
from pip._internal.models.wheel import Wheel
from pip._internal.req.req_tracker import get_requirement_tracker
from pip._internal.resolution import resolver
from pip._internal.resolution.legacy import resolver as v1_resolver
from pip._internal.utils.misc import ensure_dir, normalize_path, write_output
from pip._internal.utils.temp_dir import TempDirectory
from pip._internal.utils.typing import MYPY_CHECK_RUNNING

if MYPY_CHECK_RUNNING:
    from typing import List, Tuple
    from pip._internal.index.package_finder import PackageFinder
    from pip._internal.req.req_install import InstallRequirement


logger = logging.getLogger(__name__)


class ResolveCommand(RequirementCommand, SessionCommandMixin):
    """
    EXPERIMENTAL

    Translate the list of input requirements to a list of transitive ==
    requirements. The effect of resolving the output list of requirements
    should be the exact same as the input list, given some specific state of
    --index and --find-links urls at the time this command was run.

    This supports all of the same inputs as the `download` command.
    """

    usage = """
      %prog [options] <requirement specifier> [package-index-options] ...
      %prog [options] -r <requirements file> [package-index-options] ...
      %prog [options] <vcs project url> ...
      %prog [options] <local project path> ...
      %prog [options] <archive url/path> ..."""

    def __init__(self, *args, **kw):
        super(ResolveCommand, self).__init__(*args, **kw)

        cmd_opts = self.cmd_opts

        cmd_opts.add_option(cmdoptions.constraints())
        cmd_opts.add_option(cmdoptions.requirements())
        cmd_opts.add_option(cmdoptions.build_dir())
        cmd_opts.add_option(cmdoptions.no_deps())
        cmd_opts.add_option(cmdoptions.global_options())
        cmd_opts.add_option(cmdoptions.no_binary())
        cmd_opts.add_option(cmdoptions.only_binary())
        cmd_opts.add_option(cmdoptions.prefer_binary())
        cmd_opts.add_option(cmdoptions.src())
        cmd_opts.add_option(cmdoptions.pre())
        cmd_opts.add_option(cmdoptions.require_hashes())
        cmd_opts.add_option(cmdoptions.progress_bar())
        cmd_opts.add_option(cmdoptions.no_build_isolation())
        cmd_opts.add_option(cmdoptions.use_pep517())
        cmd_opts.add_option(cmdoptions.no_use_pep517())

        cmd_opts.add_option(
            '-d', '--dest', '--destination-dir', '--destination-directory',
            dest='download_dir',
            metavar='dir',
            default=os.curdir,
            help=("Download packages into <dir>."),
        )

        cmd_opts.add_option(
            '--v1',
            dest='v1',
            action='store_true',
            default=False,
            help=("Use the v1 resolver."),
        )

        cmd_opts.add_option(
            '--external-package-link-processor',
            dest='external_package_link_processor',
            action='store_true',
            default=False,
            help=("Delegate parsing webpages for links to a subprocess!"),
        )

        cmdoptions.add_target_python_options(cmd_opts)

        index_opts = cmdoptions.make_option_group(
            cmdoptions.index_group,
            self.parser,
        )

        self.parser.insert_option_group(0, index_opts)
        self.parser.insert_option_group(0, cmd_opts)

    class InvalidPackageUrlError(Exception):
        pass

    def _infer_package_name_and_version_from_url(self, req, finder):
        # type: (InstallRequirement, PackageFinder) -> Tuple[str, Version, str]
        name = req.req.name
        if not req.link:
            return None
        url = req.link.url
        if not url:
            return None
        link_evaluator = finder.make_link_evaluator(name)
        is_candidate, result = link_evaluator.evaluate_link(Link(url),
                                                            ignore_tags=True)
        if is_candidate:
            version = Version(result)
        else:
            wheel = Wheel(Link(url).filename)
            # name = canonicalize_name(wheel.name)
            version = None
            # raise self.InvalidPackageUrlError(result)

        return (name, version, url)

    @with_cleanup
    def run(self, options, args):
        options.ignore_installed = True
        # editable doesn't really make sense for `pip resolve`, but the bowels
        # of the RequirementSet code require that property.
        options.editables = []

        cmdoptions.check_dist_restriction(options)

        options.download_dir = normalize_path(options.download_dir)

        ensure_dir(options.download_dir)

        session = self.get_default_session(options)

        target_python = make_target_python(options)
        finder = self._build_package_finder(
            options=options,
            session=session,
            target_python=target_python,
        )
        build_delete = (not (options.no_clean or options.build_dir))

        req_tracker = self.enter_context(get_requirement_tracker())

        directory = TempDirectory(
            options.build_dir,
            delete=build_delete,
            kind="download",
            globally_managed=True,
        )

        reqs = self.get_requirements(
            args,
            options,
            finder,
            session,
        )

        preparer = self.make_requirement_preparer(
            temp_build_dir=directory,
            options=options,
            req_tracker=req_tracker,
            session=session,
            finder=finder,
            download_dir=options.download_dir,
            use_user_site=False,
            quickly_parse_sub_requirements=(
                options.quickly_parse_sub_requirements),
        )

        self.trace_basic_info(finder)

        v1_requirement_set = None
        if options.v1:
            logger.debug('using the v1 resolver!!')
            v1_resolver_instance = self.make_resolver(
                preparer=preparer,
                finder=finder,
                options=options,
                py_version_info=options.python_version,
                quickly_parse_sub_requirements=(
                    options.quickly_parse_sub_requirements),
                session=self._session,
            )
            v1_requirement_set = v1_resolver_instance.resolve(
                reqs, check_supported_wheels=True
            )
            name_version_url_sequence = [
                (self._infer_package_name_and_version_from_url(req, finder) or
                 (None, None, None))
                for req in v1_requirement_set.requirements.values()
            ]
        else:
            logger.debug('using the v2 resolver!!')
            persistent_cache_file = os.path.join(
                options.cache_dir,
                'requirement-link-dependency-cache.json')
            persistent_dependency_cache = (
                resolver.PersistentRequirementDependencyCache(
                    persistent_cache_file))
            with persistent_dependency_cache as dependency_cache:
                provider = resolver.PipProvider(
                    preparer=preparer,
                    finder=finder,
                    ignore_requires_python=False,
                    py_version_info=options.python_version,
                    session=self._session,
                    dependency_cache=dependency_cache,
                )
                input_requirements = [
                    resolver.Requirement.from_pip_requirement(r.req)
                    for r in reqs
                ]
                result = resolver.resolve(provider, input_requirements)
            name_version_url_sequence = [
                (
                    # name
                    candidate.package.decorative_name_with_extras(),
                    # version
                    candidate.version.serialize(),
                    # url
                    candidate.link.url
                )
                for candidate in result.mapping.values()
            ]

        sys.stdout.write('Resolve output:\n')
        # output_file = os.path.join(options.download_dir, 'resolve-output.txt')
        # with open(output_file, 'w') as f:
        #     f.write('{}\n'.format('\n'.join(
        #         '{}=={} ({})'.format(name, version, url)
        #         for name, version, url in name_version_url_sequence)))
        sys.stdout.write('{}\n'.format('\n'.join(
            '{}=={} ({})'.format(name, version, url)
            for name, version, url in name_version_url_sequence
            if name is not None
        )))

        return v1_requirement_set
