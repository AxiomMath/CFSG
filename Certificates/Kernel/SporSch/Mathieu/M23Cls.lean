
module

public import Certificates.Kernel.SporSch.Mathieu.M23Data
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public meta import Certificates.Kernel.SporSch.Mathieu.M23Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_classes2 CertificateChecks.KernelSporSch.M23CK 23 5 CertificateChecks.KernelSporSch.M23OC.tAM
  CertificateChecks.KernelSporSch.M23OC.tBM CertificateChecks.KernelSporSch.M23OC.tA
  CertificateChecks.KernelSporSch.M23OC.tB CertificateChecks.KernelSporSch.M23OC.repsM 2 4000

end
