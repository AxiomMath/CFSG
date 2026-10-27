module

public import Certificates.Kernel.OmegaEight.N3MCand0
public import Certificates.Kernel.OmegaEight.N3MCand1
public import Certificates.Kernel.OmegaEight.N3MCand2
public import Certificates.Kernel.OmegaEight.N3MCand3
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split
  CFSG.EvenSmallLie.OmegaEight.N3Split.MinusW

set_option maxHeartbeats 0 in
theorem cand_okN3M : candChk wN3M = true := by
  simp only [candChk, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have ht : (tuples wN3M).length = 48 := by
      simp only [tuples, wN3M, decE_toList, idK_eq, mulK_eq]
      decide +kernel
    have hc : N3Split.Minus.cases.length = 2 := rfl
    rw [candCheckW, List.all_eq_true]
    intro a ha
    rw [List.mem_range, hc] at ha
    rw [List.all_eq_true]
    intro b hb
    rw [List.mem_range, ht] at hb
    rw [Bool.and_eq_true, candP_eqN3M]
    constructor
    · simp only [linCheckWith, linRec, conPart_eq, tuples, wN3M, decE_toList, idK_eq,
        N3Split.Minus.cases, mulK_eq]
      interval_cases a <;> interval_cases b <;> decide +kernel
    · change spanAll (N3mLin a b).2.1 (N3mLin a b).2.2.length candPN3M = true
      interval_cases a
      · rcases Nat.lt_or_ge b 24 with h | h
        · exact candN3M_0 b h
        · exact candN3M_1 b h hb
      · rcases Nat.lt_or_ge b 24 with h | h
        · exact candN3M_2 b h
        · exact candN3M_3 b h hb
  · simp only [invPair, mulK_eq, idK_eq]
    decide +kernel
  · have hs2 : sortedK (decE EnN3MC2.D EnN3MC2.m).keys = true := (Enum.of_enumOK c2E_okN3M).2.1
    have h : (N3Split.Minus.samples.all fun c => enMemK EnN3MC2.D EnN3MC2.m c) = true := by
      decide +kernel
    rw [List.all_eq_true] at h ⊢
    intro c hc
    have := h c hc
    rwa [← memK_decE_eq hs2 (by decide +kernel)] at this

end CertificateChecks.KernelO8
