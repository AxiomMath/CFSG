module

public import Certificates.Kernel.SmithL6K.Pins
public import Certificates.Kernel.SmithL6K.ChecksG
public import CFSG.Certificates.Kernel.SmithL6KGSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel

theorem gns_lt : ∀ s < gns.length, gns.getD s 0 < 1953 := by
  have h := gns_ok
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro s hs
  rw [getD_of_lt hs]
  exact h.1 _ (List.getElem_mem hs)

theorem gns_zero : gns.getD 0 1 = 0 := by
  have h := gns_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem reach_gns : Reach 1953 gns.length (· == 0) (fun s u v => tvImg (gns.getD s 0) u == v) := by
  refine Reach.mono (reach_of_treeK gtr_ok) fun s hs u hu v _ he => ⟨s, hs, ?_⟩
  unfold gEdgeK at he
  rwa [tvImgP_tvImg (gns_lt s hs) hu] at he

theorem cols_getD {k a : Nat} (hk : k < 1953) (ha : a < 20) :
    (tvCols k)[a]! = (tcl.getD k []).getD a 0 := by
  rw [← tvCols_eq hk, get0]

theorem formInv_holds : chkFormInv = true := by
  refine chkFormInv_of gns_lt gns_zero reach_gns fun s hs a ha b hb => ?_
  have h := formG_ok
  unfold formGK at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hg := gns_lt s hs
  rw [cols_getD hg ha, cols_getD hg hb]
  exact h _ (by rw [getD_of_lt hs]; exact List.getElem_mem hs) a ha b hb

end CertificateChecks.KernelSmithL6K
