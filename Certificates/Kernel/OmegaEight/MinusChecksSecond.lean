module

public import Certificates.Kernel.OmegaEight.MinusW
public import Certificates.Kernel.OmegaEight.PlusNodeData
public import CFSG.Certificates.Kernel.O8NodeSound
public import CFSG.Certificates.Kernel.O8MinusSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.MinusW

@[expose] noncomputable def invS7 : List ℕ :=
  ((List.range EnS7.m).map (enKey EnS7.D)).filter fun k => k != ID12 && mul12K k k == ID12

theorem invsOf_wM7 : invsOf wM.sE7.keys = invS7 := by
  simp only [invsOf, wM, decE_toList, mulK_eq, idK_eq, invS7]

theorem invS7_length : invS7.length = 71 := by
  decide +kernel

theorem sw_eqM : PnSW = swarK := by
  have h : (PnSW == swarK) = true := by quickRfl
  exact eq_of_beq h

set_option maxHeartbeats 0 in
theorem roots7 : allRoots 2048 (invsOf wM.sE7.keys) (List.range 4096) = true := by
  have hr : List.range 4096 = (List.range 4096).filter fun _ => true :=
    (List.filter_eq_self.2 fun _ _ => rfl).symm
  have hb : ∀ v < 4096, (2 ^ 4096 - 1 : ℕ).testBit v = (fun _ => true) v := fun v hv => by
    simp [Nat.testBit_two_pow_sub_one, hv]
  rw [invsOf_wM7, hr, allRoots_eqM sw_eqM (Nat.sub_one_lt (by positivity)) hb]
  refine all_of_getD invS7_length fun i hi => ?_
  interval_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem second_okM : secondChk wM = true := by
  have hT : sortedK (decE EnS7.D EnS7.m).keys = true := (Enum.of_enumOK sE7_okM).2.1
  simp only [secondChk, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, sE7_okM⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, roots7⟩,
    mE7_okM⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, invPair, mulK_eq, idK_eq, ← Array.all_toList]
    quickRfl
  · simp only [← Array.all_toList]
    quickRfl
  · simp only [gensOK, Minus.sGens7, slpGens, runK_eq, fpowK_eq, invPair, mulK_eq, idK_eq,
      ← Array.all_toList]
    quickRfl
  · simp only [wM, decE_keys_size]
    decide +kernel
  · simp only [wM, gensIn, memK_decE_eq hT (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wM, memK_decE_eq hT (by decide +kernel)]
    quickRfl
  · simp only [wM, secondCheckW, commCount_eq, decE_keys_size, decE_getD, mulK_eq, idK_eq,
      fixLB, mulVecK_eq]
    quickRfl
  · simp only [Minus.zK, runK_eq, mulK_eq, idK_eq]
    decide +kernel
  · simp only [Minus.zK, runK_eq, fpowK_eq, idK_eq]
    decide +kernel
  · simp only [Minus.zK, runK_eq, fpowK_eq, idK_eq]
    quickRfl
  · simp only [wM, decE_keys_size]
    decide +kernel
  · simp only [wM, gensIn, memK_decE_eq hT (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wM, invFixCheckW, decE_keys_size, decE_getD, mulK_eq, idK_eq, fixLB,
      mulVecK_eq]
    quickRfl

end CertificateChecks.KernelO8
