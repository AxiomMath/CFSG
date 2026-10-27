module

public import Certificates.Kernel.SporSch.Mathieu.M22Data
public import Certificates.Kernel.SporSch.Mathieu.Gen2
public meta import Certificates.Kernel.SporSch.Mathieu.M22Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_cntord2 CertificateChecks.KernelSporSch.M22X CertificateChecks.KernelSporSch.M22Q 22 5
  CertificateChecks.KernelSporSch.M22OC.SM CertificateChecks.KernelSporSch.M22OC.baseM
  CertificateChecks.KernelSporSch.M22OC.One CertificateChecks.KernelSporSch.M22OC.oneM 2

end
