module

public import Certificates.Kernel.LocalQT.K32.D4121a
public import Certificates.Kernel.SporSch.Mathieu.Gen2
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public meta import Certificates.Kernel.LocalQT.K32.D4121a
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_classes2 CFSG.KD.LQT.M22K3 22 5 CertificateChecks.KernelSporSch.M22OC.tAM
  CertificateChecks.KernelSporSch.M22OC.tBM CertificateChecks.KernelSporSch.M22OC.tA
  CertificateChecks.KernelSporSch.M22OC.tB CFSG.KD.LQT.C4121.rep22 3 14000

#kss_cntord2 CFSG.KD.LQT.M22X3 CertificateChecks.KernelSporSch.M22Q 22 5
  CertificateChecks.KernelSporSch.M22OC.SM CertificateChecks.KernelSporSch.M22OC.baseM
  CertificateChecks.KernelSporSch.M22OC.One CertificateChecks.KernelSporSch.M22OC.oneM 3

end
