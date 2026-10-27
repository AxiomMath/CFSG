module

public import Certificates.Kernel.SporSch.J1.Levels
public import Certificates.Kernel.SporSch.J1.GenCent
public meta import Certificates.Kernel.SporSch.J1.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_ptconj CertificateChecks.KernelSporSch.J1PB CertificateChecks.KernelSporSch.J1L 3080 12
  CertificateChecks.KernelSporSch.J1.strongM CertificateChecks.KernelSporSch.J1.baseM 2000

namespace CertificateChecks.KernelSporSch.J1PB

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.MOC CFSG.KS.SporSch.J1C

theorem root : eqB 12 (mask 12) J1L.BP 3 (elJ 3080 12 (mask 12) (3080 * 12) 3 J1L.LR J1L.TR jR)
    (pg 12 (mask 12) (J1L.S 0)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.J1PB

end
