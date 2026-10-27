module

public import Certificates.Kernel.SmithEK.ChkW
public import Certificates.Kernel.SmithEK.TRowsA
public import Certificates.Kernel.SmithEK.TRowsB
public import Certificates.Kernel.SmithEK.TvEq
public import CFSG.Certificates.Kernel.SmithEK.TSound
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.SmithEK.SpanSound

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K
open CFSG.SmithL6.Kernel (get0)

#kc_forall_tree rows_allT (fun c => chunkT tp.C wd.W pts.L (64 * c) 64 = true) 14
  CertificateChecks.KernelSmithEK.c21105row_

theorem pts_len_t : pts.L.length = 693 := by
  decide +kernel

theorem wtArr_wd {i : Nat} (hi : i < 891) : wtArr[i]! = wd.W.getD i 0 := by
  have hc : i / 64 < 14 := by omega
  have e := pinChunkK_sound (pins_all (i / 64) hc) (Nat.mod_lt i (by omega : 64 > 0))
    (by rw [wData_len, Nat.div_add_mod]; exact hi)
  rw [Nat.div_add_mod] at e
  unfold pinRow at e
  simp only [Bool.and_eq_true, beq_iff_eq] at e
  rw [wtArr_get hi]
  unfold wt
  rw [wB_eq, get0, e.1.1]

theorem chkT_eq : chkT = true := by
  refine chkT_of chkW_eq (fun k hk i hi => ?_)
  have hk' : k < pts.L.length := by rw [pts_len_t]; exact hk
  have hc : i / 64 < 14 := by omega
  have hrow := chunkT_sound (rows_allT (i / 64) hc) (Nat.mod_lt i (by omega : 64 > 0))
    (by rw [wd_len, Nat.div_add_mod]; exact hi)
  rw [Nat.div_add_mod] at hrow
  have hl := laneK_sound _ _ _ _ hrow k hk'
  have hv : fld k (applyL tp.C (wd.W.getD i 0)) = applyCols (tvCols k) wtArr[i]! := by
    rw [applyL_fld, packOK_sound _ _ _ tp_ok k hk', wtArr_wd hi, tvCols_eq, ← tvW_cTabQ,
      ← cT_eq, applyCols_toArray]
  rw [hv, ← wtArr_wd hi] at hl
  have hmem : ∀ x, (wBits wd.W).testBit x = true → ∃ j < 891, wtArr[j]! = x := by
    intro x hx
    rw [wBits_testBit, List.contains_iff_mem, List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [wd_len] at hj
    refine ⟨j, hj, ?_⟩
    rw [wtArr_wd hj, List.getD_eq_getElem _ _ (by rw [wd_len]; exact hj)]
  rcases hl with hl | ⟨h1, h2⟩
  · exact Or.inl hl
  · exact Or.inr ⟨hmem _ h1, hmem _ h2⟩

end CertificateChecks.KernelSmithEK
