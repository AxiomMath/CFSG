module

public import Certificates.Kernel.SuzB17322.Checks
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSuzB17322

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor

theorem pAG : ∀ k < 4, permB 1782 11 (AE.G k) = true := by
  intro k hk
  interval_cases k <;> quickRfl

theorem cubeX : Nat.beq (pw 1782 11 X 3) (pidn 1782 11) = true := by quickRfl

theorem relX : Nat.beq (pg 11 (mask 11) X 0) 1 = true ∧
    Nat.beq (pg 11 (mask 11) (pw 1782 11 X 2) 0) 2 = true := ⟨by quickRfl, by quickRfl⟩

theorem roK : allN 6 (fun i => Nat.ble (roff 1782 (1782 * 11) (SuzC.LR i) + rcnt (SuzC.LR i))
    65536) = true := by
  decide +kernel

end CertificateChecks.KernelSuzB17322

end
