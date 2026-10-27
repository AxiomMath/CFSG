module

public import Certificates.Kernel.LocalComp.WittA2030
public import Certificates.Kernel.LocalComp.WittWords
public import Certificates.Kernel.LocalComp.WittK2034

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.KC.WCnt CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign

theorem mem_orbY1 : ∀ x : Fin 22, inM 3179043 x.val = true ↔ x ∈ orbY1 := by decide +kernel
theorem list_orbY1 : ∀ x : Fin 22, x ∈ orbY1 ↔ x.val ∈ [0, 1, 5, 9, 15, 20, 21] := by
  decide +kernel
theorem mem_orbY2 : ∀ x : Fin 22, inM 475404 x.val = true ↔ x ∈ orbY2 := by decide +kernel
theorem list_orbY2 : ∀ x : Fin 22, x ∈ orbY2 ↔ x.val ∈ [2, 3, 8, 14, 16, 17, 18] := by
  decide +kernel
theorem mem_orbY3 : ∀ x : Fin 22, inM 539840 x.val = true ↔ x ∈ orbY3 := by decide +kernel
theorem list_orbY3 : ∀ x : Fin 22, x ∈ orbY3 ↔ x.val ∈ [6, 7, 10, 11, 12, 13, 19] := by
  decide +kernel
theorem mem_pairX2 : ∀ x : Fin 22, inM 3 x.val = true ↔ x ∈ pairX2 := by decide +kernel
theorem list_pairX2 : ∀ x : Fin 22, x ∈ pairX2 ↔ x.val ∈ [0, 1] := by decide +kernel

theorem count_pres (S : Finset (Fin 22)) (X : Nat) (l : List Nat)
    (hl : ∀ x : Fin 22, x ∈ S ↔ x.val ∈ l) (hlt : ∀ i ∈ l, i < 22)
    (hX : ∀ x : Fin 22, inM X x.val = true ↔ x ∈ S) (w : List Bool) (D : Nat)
    (hD : pkw 5 (wordPerm w) = D) (e₀ e₁ e₂ : Fin 22) (h₀ : pt D e₀.val = 0)
    (h₁ : pt D e₁.val = 1) (h₂ : pt D e₂.val = 2) (m₀ : e₀ ∈ S) (m₁ : e₁ ∈ S) (m₂ : e₂ ∈ S) :
    m22Count (fun f => ∀ x ∈ S, f x ∈ S) =
      wcB (presT X l) D (inM X) (fun _ => inM X) (fun _ _ => inM X) := by
  refine m22Count_eq_wcB (fun f => ∀ x ∈ S, f x ∈ S) (presT X l)
    (fun τ => (presT_pkw τ S l X hl hlt hX).trans (decide_eq_decide.2 Iff.rfl)) (wordPerm w) (wordPerm_mem _) D hD _ _ _
    fun σ h => ?_
  rw [← mul_apply_of_pk hD σ (e := e₀) (i := 0) h₀, ← mul_apply_of_pk hD σ (e := e₁) (i := 1) h₁,
    ← mul_apply_of_pk hD σ (e := e₂) (i := 2) h₂]
  exact ⟨(hX _).2 (h _ m₀), (hX _).2 (h _ m₁), (hX _).2 (h _ m₂)⟩

theorem count_orbY :
    m22Count (fun f => ∀ x ∈ orbY1, f x ∈ orbY1) = 2520 ∧
    m22Count (fun f => ∀ x ∈ orbY2, f x ∈ orbY2) = 168 ∧
    m22Count (fun f => ∀ x ∈ orbY3, f x ∈ orbY3) = 2520 :=
  ⟨(count_pres orbY1 _ _ list_orbY1 (by decide) mem_orbY1 wO1 _ pk_wO1 0 1 5 rfl rfl rfl
      (by decide) (by decide) (by decide)).trans k2034o1,
    (count_pres orbY2 _ _ list_orbY2 (by decide) mem_orbY2 wO2 _ pk_wO2 2 3 8 rfl rfl rfl
      (by decide) (by decide) (by decide)).trans k2034o2,
    (count_pres orbY3 _ _ list_orbY3 (by decide) mem_orbY3 wO3 _ pk_wO3 6 7 10 rfl rfl rfl
      (by decide) (by decide) (by decide)).trans k2034o3⟩

theorem cov_P2 {σ : Perm (Fin 22)} (h : InP2 ⇑(σ * 1)) :
    inM 3 (σ 0).val = true ∧ inM 3 (σ 1).val = true ∧ inM 655879 (σ 2).val = true := by
  simp only [mul_one] at h
  exact ⟨(mem_pairX2 _).2 (h.2.1 0 (by decide)), (mem_pairX2 _).2 (h.2.1 1 (by decide)),
    (mem_hexad0 _).2 (h.1 2 (by decide))⟩

theorem count_P2 :
    m22Count InP2 = 128 ∧ m22Count (fun f => InP2 f ∧ f 0 = 0) = 64 ∧
    m22Count (fun f => InP2 f ∧ f 2 = 2) = 32 ∧ m22Count (fun f => InP2 f ∧ f 3 = 3) = 8 ∧
    m22Count (fun f => ∀ x ∈ pairX2, f x ∈ pairX2) = 1920 := by
  refine ⟨(m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
      fun _ h => cov_P2 h).trans k2034p,
    (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
      fun _ h => cov_P2 h.1).trans k2034p0,
    (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
      fun _ h => cov_P2 h.1).trans k2034p2,
    (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
      fun _ h => cov_P2 h.1).trans k2034p3, ?_⟩
  refine (m22Count_eq_wcB (fun f => ∀ x ∈ pairX2, f x ∈ pairX2) (presT 3 [0, 1])
    (fun τ => (presT_pkw τ pairX2 _ _ list_pairX2 (by decide) mem_pairX2).trans
      (decide_eq_decide.2 Iff.rfl)) 1 (Subgroup.one_mem _)
    _ KernelSpor.M22Syl.pk_one _ _ _ fun σ h => ?_).trans k2034x
  simp only [mul_one] at h
  exact ⟨(mem_pairX2 _).2 (h 0 (by decide)), (mem_pairX2 _).2 (h 1 (by decide)), rfl⟩

theorem facts2034 :
    (∀ x, ofTable wTab (ofTable zTab (ofTable zTab (ofTable wTab (ofTable cTab
      (ofTable zTab (ofTable wTab (ofTable cTab (ofTable cTab (ofTable cTab (ofTable zTab
      (ofTable wTab (ofTable cTab x)))))))))))) =
        List.formPerm [0, 12] (List.formPerm [1, 7] (List.formPerm [2, 15] (List.formPerm [3, 11]
          (List.formPerm [5, 21] (List.formPerm [6, 16] (List.formPerm [8, 9]
            (List.formPerm [10, 13] x)))))))
    )
    ∧ ((∀ z, ofTable yTab z = z ↔ z = 4) ∧
      (∀ z, ofTable wTab z = z ↔ z = 8 ∨ z = 12)
    )
    ∧ (∀ z : Fin 22, z ≠ 4 →
      (Finset.univ.image fun k : Fin 7 => (ofTable yTab)^[k] z) ∈ [orbY1, orbY2, orbY3]
    )
    ∧ (orbY1.card = 7 ∧ orbY2.card = 7 ∧ orbY3.card = 7)
    ∧ (m22Count (fun f => ∀ x ∈ orbY1, f x ∈ orbY1) = 2520 ∧
      m22Count (fun f => ∀ x ∈ orbY2, f x ∈ orbY2) = 168 ∧
      m22Count (fun f => ∀ x ∈ orbY3, f x ∈ orbY3) = 2520
    )
    ∧ (m22Count InP2 = 128 ∧ m22Count (fun f => InP2 f ∧ f 0 = 0) = 64 ∧
      m22Count (fun f => InP2 f ∧ f 2 = 2) = 32 ∧ m22Count (fun f => InP2 f ∧ f 3 = 3) = 8 ∧
      m22Count (fun f => ∀ x ∈ pairX2, f x ∈ pairX2) = 1920
    ) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, count_orbY,
    count_P2⟩

end CertificateChecks.KernelLC.Witt

end
