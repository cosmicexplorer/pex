# Copyright 2019 Pants project contributors (see CONTRIBUTORS.md).
# Licensed under the Apache License, Version 2.0 (see LICENSE).

"""
???
"""

from __future__ import absolute_import, print_function

import os
import re
import shutil
import sys
from abc import abstractmethod
from hashlib import sha1
from threading import Thread
from traceback import TracebackException

from pex.common import Chroot, die, grouper_it, walk_files, safe_mkdir
from pex.meta import FrozenFieldsWrapper, frozen_fields, frozen
from pex.resolver import Unsatisfiable, resolve_multi
from pex.third_party.pkg_resources import Requirement
from pex.tracer import TRACER
from pex.util import CacheHelper, DistributionHelper


@frozen_fields
class _ThreadBase(Thread, FrozenFieldsWrapper):

  class ThreadException(Exception):
    """???"""

  def __init__(self, name, log):
    super(_ThreadBase, self).__init__(name=name)
    self.log = log
    self._exc_info = None

  @frozen
  def start(self):
    super(_ThreadBase, self).start()
    return self

  @frozen
  def join(self):
    super(_ThreadBase, self).join()
    if self._exc_info:
      sys.stderr.write('\n'.join(self._exc_info.format()))
      raise self.ThreadException(f'thread {self.name} errored!')
    return self

  @frozen
  def run(self):
    try:
      self.execute()
    except Exception as e:
      self._exc_info = TracebackException.from_exception(e)

  @abstractmethod
  def execute(self):
    """???"""


### Traversing fingerprinted sources/resources in parallel!

class _TraverseThreadBase(_ThreadBase):

  def __init__(self, name, add_source_fn, cache_dir, log):
    super(_TraverseThreadBase, self).__init__(name=name, log=log)
    self.add_source = add_source_fn
    self.cache_dir = cache_dir

  def sub_thread_kwargs(self):
    return {
      'add_source_fn': self.add_source,
      'cache_dir': self.cache_dir,
      'log': self.log,
    }


class TraverseHashes(_TraverseThreadBase):

  def __init__(self, maybe_fingerprinted_module_names, **kwargs):
    super(TraverseHashes, self).__init__(name='traverse-hashes', **kwargs)
    self._maybe_fingerprinted_module_names = maybe_fingerprinted_module_names

  def execute(self):
    threads = [
      AddDirectoryEntries(module_name, directory, entries,
                          **self.sub_thread_kwargs()
                          ).start()
      for module_name, entries_by_source_root in self._maybe_fingerprinted_module_names.items()
      for directory, entries in entries_by_source_root.items()
    ]
    for t in threads:
      t.join()
      # NB: Mutation!
      self._maybe_fingerprinted_module_names[t.module_name][t.orig_directory] = t.hydrated_entries


class AddDirectoryEntries(_TraverseThreadBase):

  def __init__(self, module_name, directory, entries, **kwargs):
    assert os.path.sep not in module_name, f'fingerprinted module name {module_name} should not contain \'{os.path.sep}\'!'
    super(AddDirectoryEntries, self).__init__(name='add-directory-entries', **kwargs)
    self.module_name = module_name
    self.orig_directory = directory
    self._directory = os.path.normpath(directory)
    self._processed_entries = [
      (e['files'], e['checksum'])
      for e in entries
    ]
    self.hydrated_entries = None

  def execute(self):
    threads = [
      AddAndFingerprintSourcePaths(
        self.module_name, self._directory, source_paths, maybe_fingerprint,
        **self.sub_thread_kwargs()
      ).start()
      for source_paths, maybe_fingerprint in self._processed_entries
    ]
    self.hydrated_entries = []
    for t in threads:
      t.join()
      self.hydrated_entries.append(t.checksummed_sources)


class AddAndFingerprintSourcePaths(_TraverseThreadBase):

  def __init__(self, module_name, directory, source_paths, maybe_fingerprint, **kwargs):
    assert source_paths is not None, f"the 'files' key must be provided for module {module_name} with 'checksum' {maybe_fingerprint}!"
    super(AddAndFingerprintSourcePaths, self).__init__(name='add-and-fingerprint-source-paths',
                                                       **kwargs)
    self._module_name = module_name
    if self._module_name == '.':
      self._relpath_for_module = self._module_name
    else:
      self._relpath_for_module = self._module_name.replace('.', os.path.sep)

    self._directory = directory
    self._source_paths = source_paths
    self._maybe_fingerprint = maybe_fingerprint
    self.checksummed_sources = None

  def _walk_and_add(self, src_dir, fingerprint):
    # TODO: find a better default than 1!!!
    n_add_source_chunk_size = os.environ.get('PEX_THREAD_ADD_SOURCE_CHUNK_SIZE', 1)

    threads = [
      AddSourceSet(src_dir, list(file_group), **self.sub_thread_kwargs()).start()
      for file_group in grouper_it(n_add_source_chunk_size, walk_files(src_dir))
    ]
    all_files = []
    for t in threads:
      t.join()
      all_files.extend(t.dest_paths())
    sorted_all = sorted(all_files)
    sorted_provided = sorted(
      os.path.normpath(os.path.join(self._relpath_for_module, f))
      for f in self._source_paths
    )
    assert sorted_all == sorted_provided, f'files for module {self._module_name}, dir {self._directory}, checksum {fingerprint} in {src_dir} should have been {sorted_all}, was {sorted_provided}!'
    return sorted_all

  def execute(self):
    if self._maybe_fingerprint is not None:
      prespecified_cache_dir = os.path.join(self.cache_dir, self._maybe_fingerprint)
      self.log(f'reading {self._module_name} from prespecified_cache_dir: {prespecified_cache_dir}')
      if os.path.isdir(prespecified_cache_dir):
        sorted_sources = self._walk_and_add(prespecified_cache_dir, self._maybe_fingerprint)
        self.checksummed_sources = {
          'files': sorted_sources,
          'checksum': self._maybe_fingerprint,
        }
        return

    full_dir_path = os.path.normpath(os.path.join(self._directory, self._relpath_for_module))
    # raise Exception(f'full_dir_path: {full_dir_path}, dir: {self._directory}, relpath: {self._relpath_for_module}')
    assert os.path.isdir(full_dir_path), f'directory path {full_dir_path} does not exist! (from dir {self._directory}, module {self._module_name})'

    with TRACER.timed('hashing files in fileset'):
      # TODO: find a better default than 1!!!
      n_file_hash_chunk_size = os.environ.get('PEX_THREAD_FILE_HASH_CHUNK_SIZE', 1)
      file_hash_threads = []
      file_digest_map = {}
      for file_group in grouper_it(n_file_hash_chunk_size, self._source_paths):
        full_file_paths = [
          os.path.join(full_dir_path, f)
          for f in file_group
        ]
        file_hash_threads.append(HashFileSet(file_digest_map, full_file_paths,
                                             **self.sub_thread_kwargs())
                                 .start())
      for t in file_hash_threads:
        t.join()

    digest = sha1()
    # NB: We need to iterate over the keys in sorted order in order to ensure a consistent hash!
    for f in sorted(file_digest_map.keys()):
      digest.update(f.encode())
      digest.update(file_digest_map[f].encode())
    component_hash = digest.hexdigest()

    if self._maybe_fingerprint is not None:
      assert component_hash == self._maybe_fingerprint, f'checksum for component at {full_dir_path} was wrong: expected hash should be {component_hash}, was {self._maybe_fingerprint}! digest map was: {file_digest_map}'

    with TRACER.timed('copy files to cache dir'):
      base_cache_dir = os.path.join(self.cache_dir, component_hash)
      cache_dir = os.path.join(base_cache_dir, self._relpath_for_module)
      copy_file_threads = []
      if not os.path.isdir(cache_dir):
        safe_mkdir(cache_dir)
        # TODO: find a better default than 1!!!
        n_copy_file_chunk_size = os.environ.get('PEX_THREAD_COPY_FILE_CHUNK_SIZE', 1)
        for file_group in grouper_it(n_copy_file_chunk_size, self._source_paths):
          file_pairs = [
            (
              os.path.join(full_dir_path, f),
              os.path.join(cache_dir, f),
            )
            for f in file_group
          ]
          copy_file_threads.append(CopyFileSet(file_pairs).start())
      for t in copy_file_threads:
        t.join()

    self.log(f'reading {self._module_name} from cache_dir: {cache_dir}')
    with TRACER.timed('add sources'):
      sorted_sources = self._walk_and_add(base_cache_dir, component_hash)
    self.checksummed_sources = {
      'files': sorted_sources,
      'checksum': component_hash,
    }


class AddSourceSet(_TraverseThreadBase):

  def __init__(self, src_dir, file_group, **kwargs):
    super(AddSourceSet, self).__init__(name='add-source-set', **kwargs)
    self._src_dir = src_dir
    self._file_group = file_group

  def _parent_paths(self, dst):
    while dst != '.':
      dst = os.path.normpath(os.path.dirname(dst))
      yield dst
    yield dst

  def dest_paths(self):
    for f in self._file_group:
      yield os.path.normpath(os.path.relpath(f, self._src_dir))

  def execute(self):
    for f, dst_path in zip(self._file_group, self.dest_paths()):
      self.add_source(f, dst_path)


class HashFileSet(_TraverseThreadBase):

  def __init__(self, file_digest_map, file_group, **kwargs):
    super(HashFileSet, self).__init__(name='hash-file-set', **kwargs)
    self._file_digest_map = file_digest_map
    self._file_group = file_group

  def execute(self):
    for f in self._file_group:
      f = os.path.normpath(f)
      self._file_digest_map[f] = CacheHelper.hash(f)


class AddFingerprintedSources(_ThreadBase):

  def __init__(self, pex_builder, source_dir_hashes, resource_dir_hashes, component_cache_dir, log):
    super(AddFingerprintedSources, self).__init__(name='add-fingerprinted-sources', log=log)
    self._pex_builder = pex_builder
    # NB: these may be *modified* if they were resolved from `None` -> a fingerprint when scanning
    # source/resource directories!
    self.source_dir_hashes = source_dir_hashes
    self.resource_dir_hashes = resource_dir_hashes
    self._component_cache_dir = component_cache_dir

  def get_fingerprinted_sources(self):
    return (self.source_dir_hashes, self.resource_dir_hashes)

  def execute(self):
    with TRACER.timed('Resolving fingerprinted source/resource modules'):
      threads = [
        TraverseHashes(
          self.source_dir_hashes,
          add_source_fn=self._pex_builder.add_source,
          cache_dir=os.path.join(self._component_cache_dir, 'sources'),
          log=self.log,
        ).start(),
        TraverseHashes(
          self.resource_dir_hashes,
          add_source_fn=self._pex_builder.add_resource,
          cache_dir=os.path.join(self._component_cache_dir, 'resources'),
          log=self.log,
        ).start(),
      ]
      for t in threads:
        t.join()

    with TRACER.timed('writing out maybe-necessary __init__.py files'):
      all_file_paths = list(self._pex_builder.reverse_filesets.keys())
      all_init_py_files = frozenset(
        f for f in all_file_paths
        if os.path.basename(f) == '__init__.py'
      )
      def neighboring_init_py_paths(f):
        while f != '.':
          f = os.path.normpath(os.path.dirname(f))
          yield os.path.join(f, '__init__.py')
        yield os.path.join(f, '__init__.py')
      all_remaining_init_py_files_to_create = sorted(set(
        init_py_to_create
        for f in all_file_paths
        for init_py_to_create in neighboring_init_py_paths(f)
        if init_py_to_create not in all_init_py_files
      ))
      # TODO: consider parallelizing?
      for f in all_remaining_init_py_files_to_create:
        self._pex_builder._chroot.touch(f)



### Generic thread classes for multiple uses!

class CopyFileSet(_ThreadBase):

  def __init__(self, file_pairs):
    super(CopyFileSet, self).__init__(name='copy-file-set', log=None)
    self._file_pairs = file_pairs

  def execute(self):
    for src, dst in self._file_pairs:
      containing_dir = os.path.dirname(dst)
      safe_mkdir(containing_dir)
      shutil.copyfile(src, dst)


### Copying over fingerprinted requirements to and from the cache in parallel!

def cache_requirements(file_pairs):
  # TODO: find a better default than 1!!!
  n_cache_requirements_chunk_size = os.environ.get('PEX_THREAD_CACHE_REQUIREMENTS_CHUNK_SIZE', 1)
  cache_write_threads = [
    CopyFileSet(file_pair_group).start()
    for file_pair_group in grouper_it(n_cache_requirements_chunk_size, file_pairs)
  ]
  for t in cache_write_threads:
    t.join()


class AddFingerprintedDistRequirement(_ThreadBase):

  def __init__(self, pex_builder, dist_req_pairs, log):
    super(AddFingerprintedDistRequirement, self).__init__(name='add-fingerprinted-dist-requirement',
                                                          log=log)
    self._pex_builder = pex_builder
    self._dist_req_pairs = dist_req_pairs

  def execute(self):
    for full_dist_path, requirement in self._dist_req_pairs:
      assert os.path.isfile(full_dist_path), f'Requirement {requirement} was not found at specified path {full_dist_path}!'
      dist = DistributionHelper.distribution_from_path(full_dist_path)
      self.log(f'  {requirement} -> {dist}')
      self._pex_builder.add_distribution(dist)
      self._pex_builder.add_requirement(requirement)


def resolve_requirements_from_cache(pex_builder, dist_path_requirement_pairs, log):
  # TODO: find a better default than 1!!!
  n_resolve_cached_requirements_chunk_size = os.environ.get('PEX_THREAD_RESOLVE_CACHED_REQUIREMENTS_CHUNK_SIZE', 1)
  cache_resolve_threads = [
    AddFingerprintedDistRequirement(pex_builder, dist_req_group, log=log).start()
    for dist_req_group in grouper_it(n_resolve_cached_requirements_chunk_size, dist_path_requirement_pairs)
  ]
  for t in cache_resolve_threads:
    t.join()


class AddFingerprintedRequirements(_ThreadBase):

  def __init__(self, pex_builder, component_cache_dir, log, interpreter_constraints, resolvables,
               interpreters, platforms, cache_dir, cache_ttl, prereleases_allowed, use_manylinux):
    super(AddFingerprintedRequirements, self).__init__(name='add-fingerprinted-requirements',
                                                       log=log)
    self._pex_builder = pex_builder
    self._component_cache_dir = component_cache_dir
    self._interpreter_constraints = interpreter_constraints
    self._resolvables = resolvables
    self._interpreters = interpreters
    self._platforms = platforms
    self._cache_dir = cache_dir
    self._cache_ttl = cache_ttl
    self._prereleases_allowed = prereleases_allowed
    self._use_manylinux = use_manylinux

    self._requirements_digest = None

  @property
  def requirements_digest(self):
    if self._requirements_digest is None:
      self._requirements_digest = self._compute_requirements_digest()
    return self._requirements_digest

  def _compute_requirements_digest(self):
    requirements_digest = sha1()
    # NB: Don't hash interpreters, because they may be different across systems. Instead, hash
    # interpreter constraints!
    for constraint in self._interpreter_constraints:
      requirements_digest.update(constraint.encode())
    for resolvable in self._resolvables:
      requirements_digest.update(str(resolvable).encode())
    for platform in self._platforms:
      requirements_digest.update(platform.encode())
    requirements_digest.update(str(self._prereleases_allowed).encode())
    requirements_digest.update(str(self._use_manylinux).encode())
    all_requirements_checksum = requirements_digest.hexdigest()
    return all_requirements_checksum

  def execute(self):
    all_requirements_checksum = self.requirements_digest

    requirement_component_cache_dir = os.path.join(self._component_cache_dir,
                                                   'requirements',
                                                   all_requirements_checksum)

    if not os.path.isdir(requirement_component_cache_dir):
      with TRACER.timed('Resolving distributions and writing to fingerprinted cache'):
        try:
          resolveds = resolve_multi(self._resolvables,
                                    interpreters=self._interpreters,
                                    platforms=self._platforms,
                                    cache=self._cache_dir,
                                    cache_ttl=self._cache_ttl,
                                    allow_prereleases=self._prereleases_allowed,
                                    use_manylinux=self._use_manylinux)

          with TRACER.timed('Copying resolveds to cache'):
            safe_mkdir(requirement_component_cache_dir)
            dist_requirement_mapping_file = os.path.join(requirement_component_cache_dir, '.mapping')
            cached_resolveds_pairs = []
            with open(dist_requirement_mapping_file, 'w') as mapping_file:
              for resolved_dist in resolveds:
                req = resolved_dist.requirement
                dist = resolved_dist.distribution
                dist_filename = os.path.basename(dist.location)
                out_location = os.path.join(requirement_component_cache_dir, dist_filename)
                cached_resolveds_pairs.append((dist.location, out_location))
                # Write the dist and requirement out into the mapping file!
                mapping_file.write(f'{req}&{dist_filename}\n')
            # NB: Write the resolved requirements to the cache, in parallel!
            cache_requirements(cached_resolveds_pairs)
        except Unsatisfiable as e:
          die(e)
    assert os.path.isdir(requirement_component_cache_dir)

    with TRACER.timed('Resolving requirements from fingerprinted cache'):
      dist_requirement_mapping_file = os.path.join(requirement_component_cache_dir, '.mapping')
      dist_path_requirement_pairs = []
      with open(dist_requirement_mapping_file, 'r') as mapping_file:
        for entry in mapping_file:
          req_str, _, dist_filename = tuple(re.sub(r'\n$', '', entry).partition('&'))
          requirement = Requirement.parse(req_str)
          full_dist_path = os.path.join(requirement_component_cache_dir, dist_filename)
          dist_path_requirement_pairs.append((full_dist_path, requirement))
      resolve_requirements_from_cache(self._pex_builder, dist_path_requirement_pairs, log=self.log)
