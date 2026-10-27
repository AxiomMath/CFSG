
module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.UnitarySix.ChainArrs
meta import Certificates.Kernel.UnitarySix.ChainArrs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelU6.KQ 693 10 64 CertificateChecks.KernelU6.kStrong
  CertificateChecks.KernelU6.kBase 3 CertificateChecks.KernelU6.kDer

end
