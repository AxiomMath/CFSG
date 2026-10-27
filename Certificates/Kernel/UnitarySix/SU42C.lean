module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.UnitarySix.SU42Arrs
meta import Certificates.Kernel.UnitarySix.SU42Arrs
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib
meta import Mathlib

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelU6.SU42C 256 9 32 CertificateChecks.KernelU6.su42Strong
  CertificateChecks.KernelU6.su42Base 2 CertificateChecks.KernelU6.su42Der

end
