module

public import Certificates.Kernel.SporSch.PairBT.J2F67Data
public meta import Certificates.Kernel.SporSch.PairBT.J2F67Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_sylelts CertificateChecks.KernelSporSch.J2S5 CertificateChecks.KernelSporSch.PJ2 315 9 3
  CertificateChecks.KernelSporSch.J2F67.RL5 5 CertificateChecks.KernelSporSch.J2F67.syl5Hint

end
