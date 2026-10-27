module

public import Certificates.Kernel.SporSch.J3K426.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J3KT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow

theorem conj142200 : Nat.beq (pcomp 6156 13 (mask 13) G
    (pcomp 6156 13 (mask 13) X0 (pinvS 6156 13 (mask 13) G))) (ppw 6156 13 X0 2) = true := by
  quickRfl

theorem uNe142200 : bIf(Nat.beq U (pidn 6156 13), false, true) = true := by quickRfl

theorem vNe142200 : bIf(Nat.beq V (pidn 6156 13), false, true) = true := by quickRfl

theorem vu142200 : bIf(Nat.beq V U, false, true) = true := by quickRfl

theorem vu2142200 : bIf(Nat.beq V (ppw 6156 13 U 2), false, true) = true := by quickRfl

end CertificateChecks.KernelSporSch.J3KT

end
