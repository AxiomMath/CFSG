
module

public import Certificates.Kernel.SporSch.Mathieu.M24Data
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public meta import Certificates.Kernel.SporSch.Mathieu.M24Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_classes2 CertificateChecks.KernelSporSch.M24CK 24 5 CertificateChecks.KernelSporSch.M24OC.tAM
  CertificateChecks.KernelSporSch.M24OC.tBM CertificateChecks.KernelSporSch.M24OC.tA
  CertificateChecks.KernelSporSch.M24OC.tB CertificateChecks.KernelSporSch.M24OC.repsM 2 40000

end
