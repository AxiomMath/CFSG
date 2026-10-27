
module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.UnitarySix.ChainArrs
meta import Certificates.Kernel.UnitarySix.ChainArrs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelU6.AQ 693 10 64 CertificateChecks.KernelU6.aStrong
  CertificateChecks.KernelU6.aBase 9 CertificateChecks.KernelU6.aDer

#ks_rawchain CertificateChecks.KernelU6.SQ 693 10 64 CertificateChecks.KernelU6.sStrong
  CertificateChecks.KernelU6.aBase 13 CertificateChecks.KernelU6.sDer

#ks_rawchain CertificateChecks.KernelU6.TQ 693 10 64 CertificateChecks.KernelU6.tStrong
  CertificateChecks.KernelU6.tBase 4 CertificateChecks.KernelU6.tDer

end
