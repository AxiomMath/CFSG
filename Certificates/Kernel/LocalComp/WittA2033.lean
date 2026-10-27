module

public import Certificates.Kernel.LocalComp.WittCount
public import Certificates.Kernel.LocalComp.WittWords
public import Certificates.Kernel.LocalComp.WittK2033

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.KC.WCnt CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign

theorem pt_tZ : ∀ i : Fin 22, pt tZ i.val = (ofTable zTab i).val := by decide +kernel
theorem pt_tZs : ∀ j : Fin 11, ∀ i : Fin 22,
    pt (tZs.getD j.val 0) i.val = (ofTable zPowTabs[j.val]! i).val := by decide +kernel
theorem pt_tW : ∀ i : Fin 22, pt tW i.val = (ofTable wTab i).val := by decide +kernel
theorem pt_tWs : ∀ j : Fin 5, ∀ i : Fin 22,
    pt (tWs.getD j.val 0) i.val = (ofTable wPowTabs[j.val]! i).val := by decide +kernel
theorem pt_tY : ∀ i : Fin 22, pt tY i.val = (ofTable yTab i).val := by decide +kernel
theorem pt_tYs : ∀ j : Fin 7, ∀ i : Fin 22,
    pt (tYs.getD j.val 0) i.val = (ofTable yPowTabs[j.val]! i).val := by decide +kernel

theorem fix_wPow : ∀ j : Fin 5, j ≠ 0 → ∀ y : Fin 22, ofTable wPowTabs[j.val]! y = y →
    inM 4352 y.val = true := by decide +kernel
theorem fix_yPow : ∀ j : Fin 7, j ≠ 0 → ∀ y : Fin 22, ofTable yPowTabs[j.val]! y = y →
    Nat.beq y.val 4 = true := by decide +kernel
theorem wPow_zero : ∀ y : Fin 22, ofTable wPowTabs[(0 : Fin 5).val]! y = y := by decide +kernel
theorem yPow_zero : ∀ y : Fin 22, ofTable yPowTabs[(0 : Fin 7).val]! y = y := by decide +kernel

theorem count_tables :
    m22Count (fun g => ∀ x, g x = ofTable wTab x) = 1 ∧
    m22Count (fun g => ∀ x, g x = ofTable cTab x) = 1 ∧
    m22Count (fun g => ∀ x, g x = ofTable yTab x) = 1 := by
  refine ⟨(m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
      fun σ h => ?_).trans k2033w, (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _
      KernelSpor.M22Syl.pk_one _ _ _ fun σ h => ?_).trans k2033c,
    (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
      fun σ h => ?_).trans k2033y⟩ <;>
  · simp only [mul_one] at h
    simp only [h]
    exact ⟨rfl, rfl, rfl⟩

theorem count_norm_z :
    m22Count (fun f => ∃ j : Fin 11, ∀ x, f (ofTable zTab x) = ofTable zPowTabs[j.val]! (f x)) =
      55 := by
  refine (m22Count_eq_wcB
    (fun f => ∃ j : Fin 11, ∀ x, f (ofTable zTab x) = ofTable zPowTabs[j.val]! (f x))
    (relAny tZ tZs) (fun τ => by
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact relAny_pkw_iff τ _ tZ pt_tZ (fun j => ofTable zPowTabs[j.val]!) tZs rfl pt_tZs)
    (wordPerm wZ) (wordPerm_mem _) _ pk_wZ _ _ _ fun σ h => ?_).trans k2033nz
  obtain ⟨j, hj⟩ := h
  have e0 := mul_apply_of_pk pk_wZ σ (e := 0) (i := 0) rfl
  have e1 := mul_apply_of_pk pk_wZ σ (e := 5) (i := 1) rfl
  have e2 := mul_apply_of_pk pk_wZ σ (e := 13) (i := 2) rfl
  have z0 : ofTable zTab 0 = 5 := by decide
  have z5 : ofTable zTab 5 = 13 := by decide
  have h5 : (σ * wordPerm wZ) 5 = ofTable zPowTabs[j.val]! ((σ * wordPerm wZ) 0) := by
    rw [← z0]
    exact hj 0
  have h13 : (σ * wordPerm wZ) 13 = ofTable zPowTabs[j.val]! ((σ * wordPerm wZ) 5) := by
    rw [← z5]
    exact hj 5
  have k1 : (σ 1).val = pt (tZs.getD j.val 0) (σ 0).val := by
    rw [← e1, ← e0, h5, pt_tZs]
  have k2 : (σ 2).val = pt (tZs.getD j.val 0) (σ 1).val := by
    rw [← e2, ← e1, h13, pt_tZs]
  exact ⟨rfl, decide_eq_true ⟨j, k1⟩, decide_eq_true ⟨j, k1, k2⟩⟩

theorem count_norm_w :
    m22Count (fun f => ∃ j : Fin 5, ∀ x, f (ofTable wTab x) = ofTable wPowTabs[j.val]! (f x)) =
      20 := by
  refine (m22Count_eq_wcB
    (fun f => ∃ j : Fin 5, ∀ x, f (ofTable wTab x) = ofTable wPowTabs[j.val]! (f x))
    (relAny tW tWs) (fun τ => by
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact relAny_pkw_iff τ _ tW pt_tW (fun j => ofTable wPowTabs[j.val]!) tWs rfl pt_tWs)
    (wordPerm wW) (wordPerm_mem _) _ pk_wW _ _ _ fun σ h => ?_).trans k2033nw
  obtain ⟨j, hj⟩ := h
  have hj0 : j ≠ 0 := by
    rintro rfl
    have h0 := (hj 0).trans (wPow_zero _)
    exact absurd ((σ * wordPerm wW).injective h0) (by decide)
  have w8 : ofTable wTab 8 = 8 := by decide
  have w12 : ofTable wTab 12 = 12 := by decide
  have h8 : ofTable wPowTabs[j.val]! ((σ * wordPerm wW) 8) = (σ * wordPerm wW) 8 := by
    rw [← hj 8, w8]
  have h12 : ofTable wPowTabs[j.val]! ((σ * wordPerm wW) 12) = (σ * wordPerm wW) 12 := by
    rw [← hj 12, w12]
  rw [← mul_apply_of_pk pk_wW σ (e := 8) (i := 0) rfl,
    ← mul_apply_of_pk pk_wW σ (e := 12) (i := 1) rfl]
  exact ⟨fix_wPow j hj0 _ h8, fix_wPow j hj0 _ h12, rfl⟩

theorem count_norm_y :
    m22Count (fun f => ∃ j : Fin 7, ∀ x, f (ofTable yTab x) = ofTable yPowTabs[j.val]! (f x)) =
      21 := by
  refine (m22Count_eq_wcB
    (fun f => ∃ j : Fin 7, ∀ x, f (ofTable yTab x) = ofTable yPowTabs[j.val]! (f x))
    (relAny tY tYs) (fun τ => by
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact relAny_pkw_iff τ _ tY pt_tY (fun j => ofTable yPowTabs[j.val]!) tYs rfl pt_tYs)
    (wordPerm wY) (wordPerm_mem _) _ pk_wY _ _ _ fun σ h => ?_).trans k2033ny
  obtain ⟨j, hj⟩ := h
  have hj0 : j ≠ 0 := by
    rintro rfl
    have h0 := (hj 0).trans (yPow_zero _)
    exact absurd ((σ * wordPerm wY).injective h0) (by decide)
  have y4 : ofTable yTab 4 = 4 := by decide
  have y0 : ofTable yTab 0 = 15 := by decide
  have h4 : ofTable yPowTabs[j.val]! ((σ * wordPerm wY) 4) = (σ * wordPerm wY) 4 := by
    rw [← hj 4, y4]
  have h15 : (σ * wordPerm wY) 15 = ofTable yPowTabs[j.val]! ((σ * wordPerm wY) 0) := by
    rw [← y0]
    exact hj 0
  have e0 := mul_apply_of_pk pk_wY σ (e := 4) (i := 0) rfl
  have e1 := mul_apply_of_pk pk_wY σ (e := 0) (i := 1) rfl
  have e2 := mul_apply_of_pk pk_wY σ (e := 15) (i := 2) rfl
  have k2 : (σ 2).val = pt (tYs.getD j.val 0) (σ 1).val := by
    rw [← e2, ← e1, h15, pt_tYs]
  rw [← e0]
  exact ⟨fix_yPow j hj0 _ h4, rfl, decide_eq_true ⟨j, k2⟩⟩

theorem facts2033 :
    ((∀ x, ofTable zTab x = (CFSG.Sporadic.Mathieu.m22gA * CFSG.Sporadic.Mathieu.m22gB) x) ∧
      (∀ j : Fin 11, ∀ x, ofTable zPowTabs[j.val]! x = (ofTable zTab)^[j] x) ∧
      (∀ j : Fin 5, ∀ x, ofTable wPowTabs[j.val]! x = (ofTable wTab)^[j] x) ∧
      (∀ j : Fin 7, ∀ x, ofTable yPowTabs[j.val]! x = (ofTable yTab)^[j] x) ∧
      (∀ x, (ofTable wTab)^[5] x = x) ∧ ofTable wTab 0 ≠ 0 ∧
      (∀ x, (ofTable yTab)^[7] x = x) ∧ ofTable yTab 0 ≠ 0 ∧
      (∀ x, ofTable wTab (ofTable zTab x) = ofTable zPowTabs[9]! (ofTable wTab x)) ∧
      (∀ x, ofTable cTab (ofTable wTab x) = ofTable wPowTabs[2]! (ofTable cTab x))
    )
    ∧ (m22Count (fun g => ∀ x, g x = ofTable wTab x) = 1 ∧
      m22Count (fun g => ∀ x, g x = ofTable cTab x) = 1 ∧
      m22Count (fun g => ∀ x, g x = ofTable yTab x) = 1
    )
    ∧ (m22Count (fun f => ∃ j : Fin 11, ∀ x, f (ofTable zTab x) = ofTable zPowTabs[j.val]! (f x)) =
        55 ∧
      m22Count (fun f => ∃ j : Fin 5, ∀ x, f (ofTable wTab x) = ofTable wPowTabs[j.val]! (f x)) =
        20 ∧
      m22Count (fun f => ∃ j : Fin 7, ∀ x, f (ofTable yTab x) = ofTable yPowTabs[j.val]! (f x)) =
        21
    ) :=
  ⟨by decide +kernel, count_tables, count_norm_z, count_norm_w, count_norm_y⟩

end CertificateChecks.KernelLC.Witt

end
