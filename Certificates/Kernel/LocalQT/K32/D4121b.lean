module

public import Certificates.Kernel.LocalQT.K32.D4121a
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public meta import Certificates.Kernel.LocalQT.K32.D4121a
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_classes2 CFSG.KD.LQT.M23K3 23 5 CertificateChecks.KernelSporSch.M23OC.tAM
  CertificateChecks.KernelSporSch.M23OC.tBM CertificateChecks.KernelSporSch.M23OC.tA
  CertificateChecks.KernelSporSch.M23OC.tB CFSG.KD.LQT.C4121.rep23 3 60000

end
