
module

public import Certificates.Kernel.SporSch.Mathieu.M24BT
public import Certificates.Kernel.SporSch.Mathieu.M24Cls
public meta import Certificates.Kernel.SporSch.Mathieu.M24BT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_zscan CertificateChecks.KernelSporSch.M24ZP CertificateChecks.KernelSporSch.M24B
  CertificateChecks.KernelSporSch.M24CK 24 5 CertificateChecks.KernelSporSch.M24OC.btHint
  CertificateChecks.KernelSporSch.M24OC.tAM
  CertificateChecks.KernelSporSch.M24OC.tBM CertificateChecks.KernelSporSch.M24OC.repsM
  CertificateChecks.KernelSporSch.M24OC.pairWs 2 3 23

#kss_zscan CertificateChecks.KernelSporSch.M24ZA CertificateChecks.KernelSporSch.M24B
  CertificateChecks.KernelSporSch.M24CK 24 5 CertificateChecks.KernelSporSch.M24OC.btHint
  CertificateChecks.KernelSporSch.M24OC.tAM
  CertificateChecks.KernelSporSch.M24OC.tBM CertificateChecks.KernelSporSch.M24OC.repsM
  CFSG.Sporadic.Schreier.m24AutWords 2 3 23

end
