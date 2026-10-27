module

public import Certificates.Kernel.SporSch.HeThree.Wit
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeThree

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum

theorem kC0 : permB 8330 14 (CGX.F 0) = true := by quickRfl

theorem kC1 : permB 8330 14 (CGX.F 1) = true := by quickRfl

theorem kC2 : permB 8330 14 (CGX.F 2) = true := by quickRfl

theorem kW1 : Nat.beq (ppow 8330 14 (mask 14) (pidn 8330 14) (CGX.F 0) 3) (pidn 8330 14) = true := by
  quickRfl

theorem kW2 : Nat.beq (ppow 8330 14 (mask 14) (pidn 8330 14)
    (pcomp 8330 14 (mask 14) (pcomp 8330 14 (mask 14) (CGX.F 1) (CGX.F 2)) (CGX.F 2)) 12)
    (pidn 8330 14) = true := by
  quickRfl

theorem kW3 : Nat.beq (ppow 8330 14 (mask 14) (pidn 8330 14)
    (pcomp 8330 14 (mask 14) (pcomp 8330 14 (mask 14) (CGX.F 1) (CGX.F 1)) (CGX.F 2)) 12)
    (pidn 8330 14) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.HeThree

end
