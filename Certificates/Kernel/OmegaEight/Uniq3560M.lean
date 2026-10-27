module

public import Certificates.Data.Kernel.O8.Uniq
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeSylowData
public import Certificates.Kernel.OmegaEight.Uniq3560Data
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.SplitC

@[expose] noncomputable def wUMK : UniqWit :=
  uniqWitK 36 CFSG.EvenSmallLie.OmegaEightMinus.yIdxT CFSG.EvenSmallLie.OmegaEightMinus.invWT
    uKindM uConjM uDlM uC0M

set_option maxHeartbeats 0 in
theorem partsMK : ∀ j < 36, clsPartW 8192 (commSA CFSG.EvenSmallLie.OmegaEightMinus.saCodes)
    (conjSA CFSG.EvenSmallLie.OmegaEightMinus.saCodes) wUMK j = true := by
  intro j hj
  interval_cases j <;> decide +kernel

set_option maxHeartbeats 0 in
theorem countMK : ∀ b < 16, ((List.range (2 ^ 9)).filter fun c => decide (b * 2 ^ 9 + c < 8192) &&
    (invSA CFSG.EvenSmallLie.OmegaEightMinus.saCodes (b * 2 ^ 9 + c) &&
      decide (2 ≤ wUMK.kind (wUMK.cl (b * 2 ^ 9 + c))))).length =
    [0, 0, 6, 1, 0, 2, 4, 7, 0, 0, 0, 0, 8, 0, 0, 3].getD b 0 := by
  intro b hb
  interval_cases b <;> decide +kernel

end CertificateChecks.KernelO8
