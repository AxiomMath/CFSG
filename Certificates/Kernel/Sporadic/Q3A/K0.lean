module

public import Certificates.Kernel.Sporadic.Q3A.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Q3AK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

theorem kWt : allN 1782 (fun x => Nat.beq (wtK x) (mixK x)) = true := by quickRfl

theorem kcB0 : canonK 1782 11 (mask 11) (1782 * 11) Suz2306.B0 = true := by quickRfl
theorem kcB1 : canonK 1782 11 (mask 11) (1782 * 11) Suz2306.B1 = true := by quickRfl
theorem kcR : canonK 1782 11 (mask 11) (1782 * 11) RHO = true := by quickRfl
theorem kcX0 : canonK 1782 11 (mask 11) (1782 * 11) (Q3AX.F 0) = true := by quickRfl
theorem kcX1 : canonK 1782 11 (mask 11) (1782 * 11) (Q3AX.F 1) = true := by quickRfl
theorem kcI : allN 13 (fun j => canonK 1782 11 (mask 11) (1782 * 11) (Q3AI j)) = true := by
  quickRfl

theorem kiB0 : invEqK 1782 11 (mask 11) (1782 * 11) Suz2306.B0 (Q3AI 0) = true := by quickRfl
theorem kiB1 : invEqK 1782 11 (mask 11) (1782 * 11) Suz2306.B1 (Q3AI 1) = true := by quickRfl
theorem kiR : invEqK 1782 11 (mask 11) (1782 * 11) RHO (Q3AI 2) = true := by quickRfl
theorem kiX0 : invEqK 1782 11 (mask 11) (1782 * 11) (Q3AX.F 0) (Q3AI 3) = true := by quickRfl
theorem kiX1 : invEqK 1782 11 (mask 11) (1782 * 11) (Q3AX.F 1) (Q3AI 4) = true := by quickRfl

theorem kRho3 : Nat.beq (pcomp 1782 11 (mask 11) RHO (pcomp 1782 11 (mask 11) RHO RHO))
    (pidn 1782 11) = true := by quickRfl

theorem kF0 : f0OK = true := by quickRfl

theorem kRoots : rootsOK = true := by quickRfl

theorem kN0 : n0OK = true := by quickRfl

theorem kX0 : bAnd(Nat.beq (pcomp 1782 11 (mask 11) (Q3AX.F 0) RHO)
    (pcomp 1782 11 (mask 11) RHO (Q3AX.F 0)), OddCore.msift (Q3AX.F 0)) = true := by quickRfl

theorem kX1 : bAnd(Nat.beq (pcomp 1782 11 (mask 11) (Q3AX.F 1) RHO)
    (pcomp 1782 11 (mask 11) RHO (Q3AX.F 1)), OddCore.msift (Q3AX.F 1)) = true := by quickRfl

theorem kA1 : Bool.not (adj0K 1) = true := by quickRfl
theorem kA2 : Bool.not (adj0K 2) = true := by quickRfl
theorem kA10 : adj0K 10 = true := by quickRfl
theorem kA202 : Bool.not (adj0K 202) = true := by quickRfl

theorem kShape : allN 3 spShape = true := by quickRfl

end CertificateChecks.KernelSpor.Q3AK

end
