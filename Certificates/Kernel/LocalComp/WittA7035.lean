
module

public import Certificates.Kernel.LocalComp.WittA7040
public import Certificates.Kernel.LocalComp.WittA7041
public import Certificates.Kernel.LocalComp.WittK7035

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.KC.WCnt CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign
  CFSG.Quasithin.L34Amalgam CFSG.Quasithin.Asc94 CFSG.KC.Enum

set_option maxRecDepth 100000
theorem cbP_comm : ∀ P ∈ cbP, pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) P t1P =
    pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) t1P P := by
  decide +kernel

theorem pkM_t1 : pkM bT1 = t1P := pk_t1

theorem cb_comm : ∀ s ∈ cbWords, evalW gen (word s) * bT1 = bT1 * evalW gen (word s) := by
  have h := cbP_comm
  rw [← cbP_eq] at h
  simp only [List.forall_mem_map] at h
  simp only [← pkM_inj, pkM_mul, pkM_evalW, pkM_t1]
  exact h

theorem bWords_letters : ∀ s ∈ bWords, ∀ x ∈ word s, x.1.val < 3 := by
  decide +kernel

theorem decide_iff_eq {p : Prop} [Decidable p] {b : Bool} (h : p ↔ b = true) : b = decide p :=
  Bool.eq_iff_iff.2 (h.symm.trans decide_eq_true_iff.symm)

theorem count_B :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧
      ¬ ∃ T ∈ bTabs, ∀ x : Fin 22, σ x = T.getD x.val 0) = 0 := by
  refine (m22Count_eq_wcB _ _ (fun τ => ?_) 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k7037
  · rw [beq0_pkw, beq1_pkw, presH_pkw, decide_iff_eq (bTabs_iff τ), Bool.decide_and,
      Bool.decide_and, Bool.decide_and, _root_.decide_not, Bool.and_assoc, Bool.and_assoc]
  · rw [mul_one] at h
    rw [h.1, h.2.1]
    exact ⟨rfl, rfl, (mem_hexL _).2 (h.2.2.1 2 (by decide))⟩

theorem count_C1 :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧ ¬ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧
      (∀ x, σ (σ x) = x) ∧ ¬ ∃ T ∈ bTabs, ∀ x : Fin 22,
        T.getD (σ x).val 0 = (tab bT1).getD (T.getD x.val 0).val 0) = 0 := by
  refine (m22Count_eq_wcB _ _ (fun τ => ?_) 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k7035a
  · rw [beq0_pkw, beq1_pkw, presH_pkw, invT_pkw _ KernelSpor.M22Syl.pk_one,
      decide_iff_eq (bConj_iff τ), Bool.decide_and, Bool.decide_and, Bool.decide_and,
      Bool.decide_and, _root_.decide_not, _root_.decide_not, Bool.and_assoc, Bool.and_assoc,
      Bool.and_assoc]
  · rw [mul_one] at h
    rw [h.1, h.2.1]
    exact ⟨rfl, rfl, rfl⟩

theorem count_C2 :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 ≠ 1 ∧ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧
      (∀ x, σ (σ x) = x) ∧ ¬ ∃ T ∈ cbTabs, ∃ R ∈ repTabs, ∀ x : Fin 22,
        T.getD (σ x).val 0 = R.getD (T.getD x.val 0).val 0) = 0 := by
  refine (m22Count_eq_wcB _ _ (fun τ => ?_) 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k7035b
  · rw [beq0_pkw, beq1_pkw, presH_pkw, invT_pkw _ KernelSpor.M22Syl.pk_one,
      decide_iff_eq (cbConj_iff τ), Bool.decide_and, Bool.decide_and, Bool.decide_and,
      Bool.decide_and, _root_.decide_not, _root_.decide_not, Bool.and_assoc, Bool.and_assoc,
      Bool.and_assoc]
  · rw [mul_one] at h
    have h1 : Nat.beq (σ 1).val 1 = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]
      exact fun e => h.2.1 (Fin.ext e)
    rw [h.1, h1]
    exact ⟨rfl, by rw [(mem_hexL _).2 (h.2.2.1 1 (by decide))]; rfl,
      (mem_hexL _).2 (h.2.2.1 2 (by decide))⟩

end CertificateChecks.KernelLC.Witt

end
