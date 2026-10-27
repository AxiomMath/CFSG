module

public import Certificates.Kernel.OmegaEight.MinusCandSys0
public import Certificates.Kernel.OmegaEight.MinusCandSys1
public import Certificates.Kernel.OmegaEight.MinusCandSys2
public import Certificates.Kernel.OmegaEight.MinusCandSys3

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.MinusW

theorem cand_okM : candChk wM = true := by
  simp only [candChk, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have ht : tuplesM.length = 48 := by decide +kernel
    have hc : Minus.cases.length = 2 := rfl
    rw [candCheckW, tuples_wM, List.all_eq_true]
    intro a ha
    rw [List.mem_range, hc] at ha
    rw [List.all_eq_true]
    intro b hb
    rw [List.mem_range, ht] at hb
    have hs : candSysM a b = true := by
      interval_cases a
      · rcases Nat.lt_or_ge b 24 with h | h
        · exact candSys0 b h
        · exact candSys1 b h hb
      · rcases Nat.lt_or_ge b 24 with h | h
        · exact candSys2 b h
        · exact candSys3 b h hb
    have hl : wM.lin = MwLin := rfl
    rw [candP_eqM, hl]
    exact hs
  · simp only [invPair, mulK_eq, idK_eq]
    decide +kernel
  · have hs2 : sortedK (decE EnC2M.D EnC2M.m).keys = true := (Enum.of_enumOK c2E_okM).2.1
    have h : (Minus.samples.all fun c => enMemK EnC2M.D EnC2M.m c) = true := by decide +kernel
    rw [List.all_eq_true] at h ⊢
    intro c hc
    have := h c hc
    rwa [← memK_decE_eq hs2 (by decide +kernel)] at this

end CertificateChecks.KernelO8
