
module

public import Certificates.Kernel.SporSch.Mathieu.M23BT
public import Certificates.Kernel.SporSch.Mathieu.M23Cls
public meta import Certificates.Kernel.SporSch.Mathieu.M23BT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_zscan CertificateChecks.KernelSporSch.M23ZP CertificateChecks.KernelSporSch.M23B
  CertificateChecks.KernelSporSch.M23CK 23 5 CertificateChecks.KernelSporSch.M23OC.btHint
  CertificateChecks.KernelSporSch.M23OC.tAM
  CertificateChecks.KernelSporSch.M23OC.tBM CertificateChecks.KernelSporSch.M23OC.repsM
  CertificateChecks.KernelSporSch.M23OC.pairWs 2 4 23

#kss_zscan CertificateChecks.KernelSporSch.M23ZA CertificateChecks.KernelSporSch.M23B
  CertificateChecks.KernelSporSch.M23CK 23 5 CertificateChecks.KernelSporSch.M23OC.btHint
  CertificateChecks.KernelSporSch.M23OC.tAM
  CertificateChecks.KernelSporSch.M23OC.tBM CertificateChecks.KernelSporSch.M23OC.repsM
  CFSG.Sporadic.Schreier.m23AutWords 2 4 23

end
