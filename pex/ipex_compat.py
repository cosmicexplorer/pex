from __future__ import absolute_import

try:
  from pex.third_party.pkg_resources import *
except ModuleNotFoundError:
  from pkg_resources import *

try:
  import pex.third_party
  new_path = list(pex.third_party.expose(['pip']))
  import sys
  sys.path = new_path + sys.path
  from pex.third_party.pip._internal.legacy_resolve import MetadataOnlyResolveException
except ModuleNotFoundError:
  pass
