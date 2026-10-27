module

public import Certificates.Kernel.LocalComp.WittA7041
public import Certificates.Kernel.LocalComp.WittK7058
public import CFSG.Quasithin.Vol2.Ch5Sec2M23L34DataInputs

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.KC.WCnt CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
  CFSG.Quasithin.H13

theorem hex01_mem : ∀ h ∈ m22Hex01L, h.toFinset ∈ hexadList := by
  decide +kernel

theorem hex01_masks : ∀ x : Fin 22,
    (inM 1065035 x.val = true ↔ x ∈ [(0 : Fin 22), 1, 3, 6, 14, 20]) ∧
    (inM 270387 x.val = true ↔ x ∈ [(0 : Fin 22), 1, 4, 5, 13, 18]) ∧
    (inM 2163075 x.val = true ↔ x ∈ [(0 : Fin 22), 1, 7, 8, 16, 21]) ∧
    (inM 39939 x.val = true ↔ x ∈ [(0 : Fin 22), 1, 10, 11, 12, 15]) := by
  decide +kernel

theorem hex01_lists : ∀ x : Fin 22,
    (x ∈ [(0 : Fin 22), 1, 3, 6, 14, 20] ↔ x.val ∈ [0, 1, 3, 6, 14, 20]) ∧
    (x ∈ [(0 : Fin 22), 1, 4, 5, 13, 18] ↔ x.val ∈ [0, 1, 4, 5, 13, 18]) ∧
    (x ∈ [(0 : Fin 22), 1, 7, 8, 16, 21] ↔ x.val ∈ [0, 1, 7, 8, 16, 21]) ∧
    (x ∈ [(0 : Fin 22), 1, 10, 11, 12, 15] ↔ x.val ∈ [0, 1, 10, 11, 12, 15]) := by
  decide +kernel

theorem pres1_pkw (τ : Perm (Fin 22)) : presT 1065035 [0, 1, 3, 6, 14, 20] (pkw 5 τ) =
    decide (∀ p ∈ [(0 : Fin 22), 1, 3, 6, 14, 20], τ p ∈ [(0 : Fin 22), 1, 3, 6, 14, 20]) :=
  presL_pkw τ _ _ _ (fun x => (hex01_lists x).1) (by decide) (fun x => (hex01_masks x).1)

theorem pres2_pkw (τ : Perm (Fin 22)) : presT 270387 [0, 1, 4, 5, 13, 18] (pkw 5 τ) =
    decide (∀ p ∈ [(0 : Fin 22), 1, 4, 5, 13, 18], τ p ∈ [(0 : Fin 22), 1, 4, 5, 13, 18]) :=
  presL_pkw τ _ _ _ (fun x => (hex01_lists x).2.1) (by decide) (fun x => (hex01_masks x).2.1)

theorem pres3_pkw (τ : Perm (Fin 22)) : presT 2163075 [0, 1, 7, 8, 16, 21] (pkw 5 τ) =
    decide (∀ p ∈ [(0 : Fin 22), 1, 7, 8, 16, 21], τ p ∈ [(0 : Fin 22), 1, 7, 8, 16, 21]) :=
  presL_pkw τ _ _ _ (fun x => (hex01_lists x).2.2.1) (by decide) (fun x => (hex01_masks x).2.2.1)

theorem pres4_pkw (τ : Perm (Fin 22)) : presT 39939 [0, 1, 10, 11, 12, 15] (pkw 5 τ) =
    decide (∀ p ∈ [(0 : Fin 22), 1, 10, 11, 12, 15], τ p ∈ [(0 : Fin 22), 1, 10, 11, 12, 15]) :=
  presL_pkw τ _ _ _ (fun x => (hex01_lists x).2.2.2) (by decide) (fun x => (hex01_masks x).2.2.2)

theorem count_kernel_point :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧ ∀ h ∈ m22Hex01L, ∀ p ∈ h, σ p ∈ h) = 16 := by
  have e : ∀ σ : Fin 22 → Fin 22, (σ 0 = 0 ∧ σ 1 = 1 ∧ ∀ h ∈ m22Hex01L, ∀ p ∈ h, σ p ∈ h) ↔
      (σ 0 = 0 ∧ σ 1 = 1 ∧ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧
        (∀ p ∈ [(0 : Fin 22), 1, 3, 6, 14, 20], σ p ∈ [(0 : Fin 22), 1, 3, 6, 14, 20]) ∧
        (∀ p ∈ [(0 : Fin 22), 1, 4, 5, 13, 18], σ p ∈ [(0 : Fin 22), 1, 4, 5, 13, 18]) ∧
        (∀ p ∈ [(0 : Fin 22), 1, 7, 8, 16, 21], σ p ∈ [(0 : Fin 22), 1, 7, 8, 16, 21]) ∧
        ∀ p ∈ [(0 : Fin 22), 1, 10, 11, 12, 15], σ p ∈ [(0 : Fin 22), 1, 10, 11, 12, 15]) := by
    intro σ
    simp only [m22Hex01L, m22HexadL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
      imp_true_iff, and_true]
  refine (m22Count_eq_wcB _ _ (fun τ => ?_) 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k7058a
  · rw [Bool.eq_iff_iff, decide_eq_true_iff, e]
    simp only [beq0_pkw, beq1_pkw, presH_pkw, pres1_pkw, pres2_pkw, pres3_pkw, pres4_pkw,
      Bool.and_eq_true, decide_eq_true_iff, and_assoc]
  · rw [mul_one, e] at h
    rw [h.1, h.2.1]
    exact ⟨rfl, rfl, (mem_hexL _).2 (h.2.2.1 2 (by decide))⟩

theorem count_kernel_hexad :
    m22Count (fun σ => ∀ p ∈ m22HexadL, σ p = p) = 16 := by
  refine (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k7058b
  rw [mul_one] at h
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide)]
  exact ⟨rfl, rfl, rfl⟩

theorem count_two_hexads : ∀ h ∈ m22Hex01Others,
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
      (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ ∀ p ∈ h, σ p ∈ h) = 48 := by
  have key : ∀ (L : List (Fin 22)) (b : Nat → Bool)
      (hb : ∀ τ : Perm (Fin 22), b (pkw 5 τ) = decide (∀ p ∈ L, τ p ∈ L))
      (hk : wcB (fun y => Nat.beq (pt y 0) 0 && Nat.beq (pt y 1) 1 &&
        presT 655879 [0, 1, 2, 9, 17, 19] y && b y) KernelSpor.M22Syl.I (fun x => Nat.beq x 0)
        (fun _ x => Nat.beq x 1) (fun _ _ => inM 655879) = 48),
      m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
        (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ ∀ p ∈ L, σ p ∈ L) = 48 := by
    intro L b hb hk
    refine (m22Count_eq_wcB _ _ (fun τ => ?_) 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one
      _ _ _ fun σ h => ?_).trans hk
    · rw [beq0_pkw, beq1_pkw, presH_pkw, hb, Bool.decide_and, Bool.decide_and, Bool.decide_and,
        Bool.and_assoc, Bool.and_assoc]
    · rw [mul_one] at h
      rw [h.1, h.2.1]
      exact ⟨rfl, rfl, (mem_hexL _).2 (h.2.2.1 2 (by decide))⟩
  intro h hh
  simp only [m22Hex01Others, m22Hex01L, List.tail_cons, List.mem_cons, List.not_mem_nil,
    or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · exact key [0, 1, 3, 6, 14, 20] (presT 1065035 [0, 1, 3, 6, 14, 20]) pres1_pkw k7058c1
  · exact key [0, 1, 4, 5, 13, 18] (presT 270387 [0, 1, 4, 5, 13, 18]) pres2_pkw k7058c2
  · exact key [0, 1, 7, 8, 16, 21] (presT 2163075 [0, 1, 7, 8, 16, 21]) pres3_pkw k7058c3
  · exact key [0, 1, 10, 11, 12, 15] (presT 39939 [0, 1, 10, 11, 12, 15]) pres4_pkw k7058c4

end CertificateChecks.KernelLC.Witt

end
