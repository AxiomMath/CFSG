module

public import Certificates.Kernel.SporSch.J3K426.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J3KT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow

theorem comm5170 : Nat.beq (pcomp 6156 13 (mask 13) (L 4) X1)
    (pcomp 6156 13 (mask 13) X1 (L 4)) = true := by
  quickRfl

theorem ne5170 : bIf(Nat.beq (L 4) X1, false, true) = true := by quickRfl

theorem ne5170sq : bIf(Nat.beq (L 4) (ppw 6156 13 X1 2), false, true) = true := by quickRfl

end CertificateChecks.KernelSporSch.J3KT

end
