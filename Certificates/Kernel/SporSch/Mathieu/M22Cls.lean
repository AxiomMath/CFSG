module

public import Certificates.Kernel.SporSch.Mathieu.M22Data
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public meta import Certificates.Kernel.SporSch.Mathieu.M22Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_classes2 CertificateChecks.KernelSporSch.M22CK 22 5 CertificateChecks.KernelSporSch.M22OC.tAM
  CertificateChecks.KernelSporSch.M22OC.tBM CertificateChecks.KernelSporSch.M22OC.tA
  CertificateChecks.KernelSporSch.M22OC.tB CertificateChecks.KernelSporSch.M22OC.repsM 2 2000

end
