# Copyright 2019 Pants project contributors (see CONTRIBUTORS.md).
# Licensed under the Apache License, Version 2.0 (see LICENSE).

"""
???
"""

from __future__ import absolute_import, print_function

from functools import wraps

from pex.compatibility import AbstractClass


def frozen(func):
  func._is_frozen_field = True
  return func


class FrozenFieldsWrapper(AbstractClass):
  _source_class = None
  _frozen_fields = None

  def validate_frozen_fields(self):
    for f in self._frozen_fields:
      if not getattr(getattr(self, f), '_is_frozen_field', False):
        raise TypeError(f'field {f} was marked @frozen in superclass {self._source_class.__name__}, but overriden in subclass {type(self).__name__}!')


def frozen_fields(cls):
  cls._source_class = cls
  cls._frozen_fields = [
    k
    for k, v in cls.__dict__.items()
    if getattr(v, '_is_frozen_field', False)
  ]
  prev_init = cls.__init__
  @wraps(prev_init)
  def new_init(self, *args, **kwargs):
    self.validate_frozen_fields()
    prev_init(self, *args, **kwargs)
  cls.__init__ = new_init
  return cls
