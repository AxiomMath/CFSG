module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.KGroups.U33Data
meta import Certificates.Kernel.Misc.KGroups.U33Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelMisc.U33PC 28 5 28 CertificateChecks.KernelMisc.U33K.pStrong
  CertificateChecks.KernelMisc.U33K.pBase 2 CertificateChecks.KernelMisc.U33K.pDer

#ks_rawchain CertificateChecks.KernelMisc.U33AC 28 5 28 CertificateChecks.KernelMisc.U33K.aStrong
  CertificateChecks.KernelMisc.U33K.aBase 3 CertificateChecks.KernelMisc.U33K.aDer

end
