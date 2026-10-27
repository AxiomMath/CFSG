module

public import Certificates.Kernel.SmithL6K.ChecksS
public import Certificates.Kernel.SmithL6K.ChecksS1
public import Certificates.Kernel.SmithL6K.ChecksS2
public import Certificates.Kernel.SmithL6K.ChecksS3
public import Certificates.Kernel.SmithL6K.ChecksS4
public import Certificates.Kernel.SmithL6K.GlueF
public import Certificates.Kernel.SmithL6K.GlueA
public import CFSG.Certificates.Kernel.SmithL6KSSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel
open CFSG.SmithE (applyCols spanData)

theorem sTvArr_eq {k : Nat} (hk : k < 1953) : tvArr[k]! = (tcl.getD k []).toArray := by
  rw [tvArr_get hk, ← tvCols_eq hk, Array.toArray_toList]

theorem sTcl_len {k : Nat} (hk : k < 1953) : (tcl.getD k []).length = 20 := by
  rw [← tvCols_eq hk, Array.length_toList, tvCols_size]

theorem sMap_get {α β : Type} [Inhabited α] [Inhabited β] (T : Array α) (f : α → β) {k : Nat}
    (hk : k < T.size) : (T.map f)[k]! = f T[k]! := by
  rw [getElem!_pos _ k (by rw [Array.size_map]; exact hk), Array.getElem_map, getElem!_pos T k hk]

theorem sSpanArr_eq {k : Nat} (hk : k < 1953) :
    mfSpanArr[k]! = spanData (tcl.getD k []).toArray := by
  have hs : k < tvArr.size := by
    unfold tvArr
    rw [Array.size_ofFn]
    exact hk
  unfold mfSpanArr
  rw [sMap_get tvArr spanData hs, sTvArr_eq hk]

theorem sZip_get {l : Nat} (hl : l < 1953) (h3 : l < (tvc.zip tcl).length) :
    (tvc.zip tcl)[l] = (tvc.getD l 0, tcl.getD l []) := by
  rw [List.getElem_zip, getD_of_lt (by rw [tvc_length]; exact hl),
    getD_of_lt (by rw [sTcl_length]; exact hl)]

theorem sZip_mem_chunk {l lo n : Nat} (hl : l < 1953) (h1 : lo ≤ l) (h2 : l < lo + n) :
    (tvc.getD l 0, tcl.getD l []) ∈ ((tvc.zip tcl).drop lo).take n := by
  have hz : (tvc.zip tcl).length = 1953 := by rw [List.length_zip, tvc_length, sTcl_length]; rfl
  have h4 : l - lo < (((tvc.zip tcl).drop lo).take n).length := by
    rw [List.length_take, List.length_drop, hz]
    omega
  have e : (((tvc.zip tcl).drop lo).take n)[l - lo] = (tvc.getD l 0, tcl.getD l []) := by
    rw [List.getElem_take, List.getElem_drop]
    have e2 : (tvc.zip tcl)[lo + (l - lo)]'(by rw [hz]; omega) =
        (tvc.zip tcl)[l]'(by rw [hz]; omega) := by
      congr 1
      omega
    rw [e2, sZip_get hl]
  rw [← e]
  exact List.getElem_mem h4

theorem sRow_all {l : Nat} (hl : l < 1953) (h0 : l ≠ 0) :
    sRowK (tcl.getD 0 []) ((sEchL (tcl.getD 0 [])).map (·.2)) (maskOf wtd) (tvc.getD 0 0)
      (tvc.getD l 0, tcl.getD l []) = true := by
  have key : ∀ lo n, sRowsK tvc tcl (maskOf wtd) lo n = true → lo ≤ l → l < lo + n →
      sRowK (tcl.getD 0 []) ((sEchL (tcl.getD 0 [])).map (·.2)) (maskOf wtd) (tvc.getD 0 0)
        (tvc.getD l 0, tcl.getD l []) = true := fun lo n h h1 h2 =>
    List.all_eq_true.mp h _ (sZip_mem_chunk hl h1 h2)
  rcases Nat.lt_or_ge l 489 with c1 | c1
  · exact key 1 488 sRows1_ok (by omega) (by omega)
  rcases Nat.lt_or_ge l 977 with c2 | c2
  · exact key 489 488 sRows2_ok c1 (by omega)
  rcases Nat.lt_or_ge l 1465 with c3 | c3
  · exact key 977 488 sRows3_ok c2 (by omega)
  · exact key 1465 488 sRows4_ok c3 (by omega)

theorem mfChkPair0_holds : mfChkPair0 = true := by
  unfold mfChkPair0
  refine List.all_eq_true.mpr fun l hl => ?_
  have hl' := List.mem_range.mp hl
  rw [kind_eq hl', sTvArr_eq (k := 0) (by decide), sTvArr_eq hl']
  by_cases h0 : l = 0
  · subst h0
    exact pair_of sPair00_ok
  · exact pair_of (sRowK_parts (sRow_all hl' h0)).1

theorem mfChkSpan_holds : mfChkSpan = true := by
  unfold mfChkSpan
  refine List.all_eq_true.mpr fun k hk => ?_
  have hk' := List.mem_range.mp hk
  rw [sSpanArr_eq hk', sTvArr_eq hk']
  refine spanBody_of (CFSG.SmithE.K.spanOKA_of (sTcl_len hk') ?_)
  by_cases h0 : k = 0
  · subst h0
    exact sSpan0_ok
  · exact (sRowK_parts (sRow_all hk' h0)).2.1

theorem sIsWt_of (v : Nat) (h : (maskOf wtd).testBit v = true) : mfIsWt v = true := by
  unfold maskOf at h
  rw [maskOf_testBit, Nat.zero_testBit, Bool.false_or, List.contains_iff_mem] at h
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
  have hi' : i < 1395 := by rw [wtd_length] at hi; exact hi
  rw [isWt_iff]
  refine ⟨i, hi', ?_⟩
  rw [← wtd_get hi', getD_of_lt hi]
  exact e

theorem mfChkInt0_holds : mfChkInt0 = true := by
  unfold mfChkInt0
  refine List.all_eq_true.mpr fun l hl => ?_
  have hl' := List.mem_range.mp hl
  by_cases h0 : l = 0
  · subst h0
    rfl
  rw [sSpanArr_eq (k := 0) (by decide), sSpanArr_eq hl', kind_eq hl']
  have e : decide (l = 0) = false := decide_eq_false h0
  rw [e, Bool.false_or]
  exact int0_of (sTcl_len (by decide)) (sTcl_len hl') sIsWt_of
    (sRowK_parts (sRow_all hl' h0)).2.2

end CertificateChecks.KernelSmithL6K
