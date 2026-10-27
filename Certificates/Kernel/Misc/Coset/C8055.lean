module

public import CFSG.Timmesfeld.Exceptional.DeepQData
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.Kernel.Misc.Coset.MemSound
public import Certificates.Kernel.Misc.Coset.XQW
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.CosetTablePresented
public import CFSG.Certificates.WordPresentation
public import Mathlib

public section

namespace CertificateChecks.KernelMiscCoset.C8055

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Timmesfeld.Moufang.Deep CFSG.Certificates

theorem t : relsQ.map encW = CFSG.KBRoute.XQW.rels := by decide +kernel
theorem w : CFSG.KBRoute.XQW.T1.words = (subsetOf 3 [0, 1]).map fun x => [(x.val, true)] := by
  decide +kernel
theorem codes_eq : (encW wQC6).map Mem.codeN =
    [4, 2, 0, 3, 1, 4, 2, 0, 3, 1, 4, 2, 0, 3, 1, 4, 2, 0, 3, 1, 4, 2, 0, 3, 1, 4, 2, 0, 3, 1] := by
  decide +kernel

theorem walk_ok : Mem.memOK CFSG.KBData.XQW_T1v.F 3464816
    [4, 2, 0, 3, 1, 4, 2, 0, 3, 1, 4, 2, 0, 3, 1, 4, 2, 0, 3, 1, 4, 2, 0, 3, 1, 4, 2, 0, 3, 1]
    [0, 6, 26, 86, 2695169, 436, 2700024, 2702015, 3612, 2702023, 2770190, 16055, 16052, 40072,
      6104713, 2770189, 2700497, 5187, 2700029, 1395, 2695320, 145, 47, 13, 3, 2695132, 2695130,
      2695128, 2695131, 2695129] = true := by quickRfl

theorem mem : PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ relsQ.map FreeGroup.mk}
    (FreeGroup.mk wQC6) ∈ genSub {r : FreeGroup (Fin 3) | r ∈ relsQ.map FreeGroup.mk}
      (subsetOf 3 [0, 1]) := by
  have h := XQW.t1
  unfold CFSG.KBRoute.XQW.T1.ok at h
  have hm := Mem.memOK_sound (pgGen relsQ) (sword_rels relsQ t) h (by norm_num)
    CFSG.KBRoute.XQW.top (u := encW wQC6) (by
      intro l hl
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
      exact x.1.isLt) (by rw [codes_eq]; exact walk_ok)
  rw [sword_pgGen, w, wordSub_letters] at hm
  exact hm

end CertificateChecks.KernelMiscCoset.C8055

end
