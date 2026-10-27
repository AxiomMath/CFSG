module

public import Certificates.Kernel.SporSch.J1.Levels
public import Certificates.Kernel.SporSch.J1.GenPt
public meta import Certificates.Kernel.SporSch.J1.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_ptcnt CertificateChecks.KernelSporSch.J1PC CertificateChecks.KernelSporSch.J1L 3080 12
  CertificateChecks.KernelSporSch.J1.strongM CertificateChecks.KernelSporSch.J1.baseM 2 3 7 19

end
