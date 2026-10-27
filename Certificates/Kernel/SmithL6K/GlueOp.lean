module

public import Certificates.Kernel.SmithL6K.ChecksOp
public import Certificates.Kernel.SmithL6K.GlueT
public import Certificates.Kernel.SmithL6K.GlueW
public import CFSG.Certificates.Kernel.SmithL6KOpSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K
open CFSG.SmithE (applyCols)

theorem prStd_holds : prChkStd = true := chkStd_of hC op_std_ok

theorem prOrd4_holds : prChkOrd4 = true := chkOrd4_of hC op_ord4_ok

theorem tcl_toArray {k : Nat} (hk : k < 1953) : (tcl.getD k []).toArray = tvCols k := by
  rw [← tvCols_eq hk, Array.toArray_toList]

theorem prIdxK_eq (k : Nat) : prIdxK wtP (wedge3 1 2 (tvPair k).1) = prIdx k := by
  unfold prIdxK prIdx prW
  rw [find?_congr (q := fun i => wt i == wedge3 1 2 (tvPair k).1)
    fun i hi => by rw [wtP_eq (List.mem_range.mp hi)]]

theorem prF3_holds : prChkF3 = true := by
  have h := op_f3_ok
  unfold f3K at h
  unfold prChkF3
  simp only [List.all_eq_true, List.mem_range] at h ⊢
  intro k hk
  have hk' := h k hk
  rw [tvImgP_tvImg (a := 0) hk (by decide), tvImgP_tvImg (a := 31) hk (by decide),
    tcl_toArray hk, tcl_toArray (k := 0) (by decide), tcl_toArray (k := 31) (by decide),
    pairK_eq hC hk, prIdxK_eq] at hk'
  by_cases hg : (tvImg k 0 == 0 && tvImg k 31 == 31) = true
  · rw [hg] at hk' ⊢
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hk' ⊢
    obtain ⟨⟨⟨hr, h1⟩, h2⟩, h3⟩ := hk'
    rw [← wtP_eq hr]
    exact ⟨⟨⟨⟨hr, wedge3_lt20 1 2 (prU k)⟩, h1⟩, h2⟩, h3⟩
  · rw [Bool.eq_false_iff.mpr hg]
    rfl

end CertificateChecks.KernelSmithL6K
