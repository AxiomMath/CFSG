module

public import Certificates.Data.Kernel.O8.Uniq
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylowData
public import Certificates.Kernel.OmegaEight.Uniq3560Data
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.SplitC

@[expose] noncomputable def wUPK : UniqWit :=
  uniqWitK 38 CFSG.EvenSmallLie.OmegaEight.yIdxT CFSG.EvenSmallLie.OmegaEight.invWT uKindP uConjP
    uDlP uC0P

set_option maxHeartbeats 0 in
theorem partsPK : ∀ j < 38, clsPartW 8192 (commSA CFSG.EvenSmallLie.OmegaEight.saCodes)
    (conjSA CFSG.EvenSmallLie.OmegaEight.saCodes) wUPK j = true := by
  intro j hj
  interval_cases j <;> decide +kernel

set_option maxHeartbeats 0 in
theorem countPK : ∀ b < 16, ((List.range (2 ^ 9)).filter fun c => decide (b * 2 ^ 9 + c < 8192) &&
    (invSA CFSG.EvenSmallLie.OmegaEight.saCodes (b * 2 ^ 9 + c) &&
      decide (2 ≤ wUPK.kind (wUPK.cl (b * 2 ^ 9 + c))))).length =
    [0, 3, 0, 3, 8, 1, 0, 0, 3, 5, 0, 0, 0, 3, 2, 3].getD b 0 := by
  intro b hb
  interval_cases b <;> decide +kernel

end CertificateChecks.KernelO8
