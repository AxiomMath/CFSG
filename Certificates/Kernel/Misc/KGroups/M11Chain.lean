module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.KGroups.M11Data
meta import Certificates.Kernel.Misc.KGroups.M11Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelMisc.M11C 11 4 11 CertificateChecks.KernelMisc.M11K.m11Strong
  CertificateChecks.KernelMisc.M11K.m11Base 2 CertificateChecks.KernelMisc.M11K.m11Der

end
