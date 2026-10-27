module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.UnitarySix.M22Arrs
meta import Certificates.Kernel.UnitarySix.M22Arrs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelU6.M22C 22 5 22 CertificateChecks.KernelU6.m22Strong
  CertificateChecks.KernelU6.m22Base 2 CertificateChecks.KernelU6.m22Der

end
