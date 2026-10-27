module

public import Certificates.Kernel.SporSch.Mathieu.M22OData
public meta import Certificates.Kernel.SporSch.Mathieu.M22OData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_cntord2 CertificateChecks.KernelSporSch.M22OX CertificateChecks.KernelSporSch.M22Q 22 5
  CertificateChecks.KernelSporSch.M22OC.SM CertificateChecks.KernelSporSch.M22OC.baseM
  CertificateChecks.KernelSporSch.M22D CertificateChecks.KernelSporSch.M22OC.tDM 2

#kss_cntcomm CertificateChecks.KernelSporSch.M22OZ CertificateChecks.KernelSporSch.M22Q 22 5
  CertificateChecks.KernelSporSch.M22OC.SM CertificateChecks.KernelSporSch.M22OC.baseM
  CertificateChecks.KernelSporSch.M22D CertificateChecks.KernelSporSch.M22OC.tDM
  CertificateChecks.KernelSporSch.M22OC.A0 CertificateChecks.KernelSporSch.M22OC.tAM
  CertificateChecks.KernelSporSch.M22OC.B0 CertificateChecks.KernelSporSch.M22OC.tBM

end
