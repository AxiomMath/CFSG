
module

public import Certificates.Kernel.SporSch.Mathieu.M24Data
public import Certificates.Kernel.SporSch.Mathieu.GenBT
public meta import Certificates.Kernel.SporSch.Mathieu.M24Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_oddB CertificateChecks.KernelSporSch.M24O1 CertificateChecks.KernelSporSch.M24C1 24 5
  CertificateChecks.KernelSporSch.M24OC.SC1 CertificateChecks.KernelSporSch.M24OC.baseC1 15 512

#kss_oddB CertificateChecks.KernelSporSch.M24O2 CertificateChecks.KernelSporSch.M24C2 24 5
  CertificateChecks.KernelSporSch.M24OC.SC2 CertificateChecks.KernelSporSch.M24OC.baseC2 21 512

end
