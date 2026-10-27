module

public import Certificates.Kernel.OmegaEight.Uniq3560M
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.SplitC

set_option maxHeartbeats 0 in
theorem rowsMK : ∀ j < 36, ∀ b < 16, ((List.range (2 ^ 9)).all fun c =>
    !(decide (b * 2 ^ 9 + c < 8192)) ||
      dRowW (commSA CFSG.EvenSmallLie.OmegaEightMinus.saCodes) wUMK j (b * 2 ^ 9 + c)) = true := by
  intro j hj b hb
  interval_cases j <;> interval_cases b <;> decide +kernel

set_option maxHeartbeats 0 in
theorem pairsMK : ∀ j < 36, ∀ b < 8, ((List.range (2 ^ 4)).all fun c =>
    !(decide (b * 2 ^ 4 + c < 128)) ||
      dPairW (commSA CFSG.EvenSmallLie.OmegaEightMinus.saCodes) wUMK j (b * 2 ^ 4 + c)) = true := by
  intro j hj b hb
  interval_cases j <;> interval_cases b <;> decide +kernel

end CertificateChecks.KernelO8
