
module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.UnitarySix.ChainArrs
meta import Certificates.Kernel.UnitarySix.ChainArrs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelU6.PQ 693 10 64 CertificateChecks.KernelU6.pStrong
  CertificateChecks.KernelU6.pBase 12 CertificateChecks.KernelU6.pDer

end
