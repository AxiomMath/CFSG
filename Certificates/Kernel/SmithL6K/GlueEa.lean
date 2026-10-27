module

public import Certificates.Kernel.SmithL6K.ChecksEa
public import Certificates.Kernel.SmithL6K.GlueT
public import Certificates.Kernel.SmithL6K.GlueW
public import CFSG.Certificates.Kernel.SmithL6KEaSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K
open CFSG.SmithE (applyCols)

theorem tcl_arr {k : Nat} (hk : k < 1953) : (tcl.getD k []).toArray = tvCols k := by
  rw [← tvCols_eq hk, Array.toArray_toList]

theorem eaC8_holds : eaChkC8 = true := by
  have h := ea_c8_ok
  unfold c8K at h
  rw [tcl_arr (k := 0) (by decide), tcl_arr (k := 31) (by decide)] at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  obtain ⟨hb, hl⟩ := h
  have hlow : ∀ j < 4096, (applyCols (tvCols 0) (16 * j) = 16 * j ∧
      applyCols (tvCols 31) (16 * j) = 16 * j) ↔ j = 0 := by
    intro j hj
    have e := hl j hj
    rw [Bool.eq_iff_iff] at e
    simpa using e
  unfold eaChkC8
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  intro c hc
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact fixed_iff_supp (fun m hm => (hb m hm).1) (fun m hm => (hb m hm).2) hlow hc

theorem eaW_holds : eaChkW = true := by
  have h := ea_w_ok
  unfold wK at h
  unfold eaChkW
  simp only [List.all_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq] at h ⊢
  intro m hm
  obtain ⟨i, hi, e⟩ := h m hm
  exact ⟨i, hi, by rw [← wtP_eq hi]; exact e⟩

theorem eaF4_holds : eaChkF4 = true := by
  have h := ea_f4_ok
  have hmem : ∀ p ∈ eaIK tcP idxP, p < 1953 := fun p hp => by
    unfold eaIK at hp
    exact List.mem_range.mp (List.mem_filter.mp hp).1
  unfold f4K at h
  unfold eaChkF4 eaRestr
  rw [eaI_eq hC hI]
  rw [List.map_congr_left (l := eaIK tcP idxP)
    (g := fun p => (p, eaBits.map fun m => applyCols (tcl.getD p []).toArray (2 ^ m)))
    fun p hp => by rw [tcl_arr (hmem p hp)]]
  exact h

theorem eaRig_holds : eaChkRig = true := chkRig_of hC hI ea_rig1_ok ea_rig2_ok

end CertificateChecks.KernelSmithL6K
