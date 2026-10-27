module

public import Certificates.Kernel.LocalComp.WittCount
public import Certificates.Kernel.LocalComp.WittK7041
public import CFSG.Certificates.Kernel.WittConjSound
public import CFSG.Quasithin.Recognition.M22UniqueDataInputs

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.KC.WCnt CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

theorem list_hexL : ∀ x : Fin 22, x ∈ m22HexadL ↔ x.val ∈ [0, 1, 2, 9, 17, 19] := by
  decide +kernel

theorem mem_hexL : ∀ x : Fin 22, inM 655879 x.val = true ↔ x ∈ m22HexadL := by
  decide +kernel

theorem presH_pkw (τ : Perm (Fin 22)) : presT 655879 [0, 1, 2, 9, 17, 19] (pkw 5 τ) =
    decide (∀ p ∈ m22HexadL, τ p ∈ m22HexadL) :=
  presL_pkw τ _ _ _ list_hexL (by decide) mem_hexL

theorem beq0_pkw (τ : Perm (Fin 22)) : Nat.beq (pt (pkw 5 τ) 0) 0 = decide (τ 0 = 0) :=
  beq_pt_pkw τ 0 0

theorem beq1_pkw (τ : Perm (Fin 22)) : Nat.beq (pt (pkw 5 τ) 1) 1 = decide (τ 1 = 1) :=
  beq_pt_pkw τ 1 1

theorem pt_F1P : ∀ i : Fin 22, pt F1P i.val = (m22F1 i).val := by decide +kernel
theorem pt_F2P : ∀ i : Fin 22, pt F2P i.val = (m22F2 i).val := by decide +kernel

theorem count_two_point :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1) = 960 := by
  refine (m22Count_eq_wcB _ _ (fun τ => ?_) 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k7041a
  · rw [beq0_pkw, beq1_pkw, Bool.decide_and]
  · rw [mul_one] at h
    rw [h.1, h.2]
    exact ⟨rfl, rfl, rfl⟩

theorem count_two_point_hexad :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧ ∀ p ∈ m22HexadL, σ p ∈ m22HexadL) = 192 := by
  refine (m22Count_eq_wcB _ _ (fun τ => ?_) 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k7041b
  · rw [beq0_pkw, beq1_pkw, presH_pkw, Bool.decide_and, Bool.decide_and, Bool.and_assoc]
  · rw [mul_one] at h
    rw [h.1, h.2.1]
    exact ⟨rfl, rfl, (mem_hexL _).2 (h.2.2 2 (by decide))⟩

theorem count_centralizer :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
      (∀ p : Fin 22, σ (m22F1 p) = m22F1 (σ p)) ∧ ∀ p : Fin 22, σ (m22F2 p) = m22F2 (σ p)) = 1 := by
  refine (m22Count_eq_wcB _ _ (fun τ => ?_) 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k7041c
  · rw [beq0_pkw, beq1_pkw, relT_pkw τ m22F1 m22F1 F1P F1P pt_F1P pt_F1P,
      relT_pkw τ m22F2 m22F2 F2P F2P pt_F2P pt_F2P, Bool.decide_and, Bool.decide_and,
      Bool.decide_and, Bool.and_assoc, Bool.and_assoc]
  · rw [mul_one] at h
    rw [h.1, h.2.1]
    exact ⟨rfl, rfl, rfl⟩

theorem count_ptHex :
    m22Count (fun σ => σ 0 = 0 ∧ ∀ p ∈ m22HexadL, σ p ∈ m22HexadL) = 960 := by
  refine (m22Count_eq_wcB _ _ (fun τ => ?_) 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k7042a
  · rw [beq0_pkw, presH_pkw, Bool.decide_and]
  · rw [mul_one] at h
    rw [h.1]
    exact ⟨rfl, (mem_hexL _).2 (h.2 1 (by decide)), (mem_hexL _).2 (h.2 2 (by decide))⟩

theorem facts7041 :
    ((m22Tbar : Equiv.Perm (Fin 22)) 0 = 1 ∧
       (m22Tbar : Equiv.Perm (Fin 22)) 1 = 0 ∧ PresHex m22Tbar)
    ∧ ((m22I1 : Equiv.Perm (Fin 22)) 0 = 1 ∧
       (m22I1 : Equiv.Perm (Fin 22)) 1 = 2 ∧ PresHex m22I1)
    ∧ ((m22I2 : Equiv.Perm (Fin 22)) 0 = 2 ∧
       (m22I2 : Equiv.Perm (Fin 22)) 1 = 0 ∧ PresHex m22I2)
    ∧ (((m22Fix2 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Fix2 : Equiv.Perm (Fin 22)) 1 = 2 ∧
         PresHex m22Fix2) ∧
       ((m22Fix9 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Fix9 : Equiv.Perm (Fin 22)) 1 = 9 ∧
         PresHex m22Fix9) ∧
       ((m22Fix17 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Fix17 : Equiv.Perm (Fin 22)) 1 = 17 ∧
         PresHex m22Fix17) ∧
       ((m22Fix19 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Fix19 : Equiv.Perm (Fin 22)) 1 = 19 ∧
         PresHex m22Fix19))
    ∧ ((m22G : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22G : Equiv.Perm (Fin 22)) 1 = 1 ∧
       (∀ p : Fin 22, (m22G : Equiv.Perm (Fin 22)) p ∈ m22HexadF ↔ p ∈ m22H1F) ∧
       ¬ PresHex m22G)
    ∧ ((∀ p, (m22E1 : Equiv.Perm (Fin 22)) p = m22F1 p) ∧
       ∀ p, (m22E2 : Equiv.Perm (Fin 22)) p = m22F2 p)
    ∧ ((m22F1 0 = 0 ∧ m22F1 1 = 1 ∧ (∀ p, m22F1 p ∈ m22HexadF ↔ p ∈ m22HexadF) ∧
         ∀ p, m22F1 p ∈ m22H1F ↔ p ∈ m22H1F) ∧
       (m22F2 0 = 0 ∧ m22F2 1 = 1 ∧ (∀ p, m22F2 p ∈ m22HexadF ↔ p ∈ m22HexadF) ∧
         ∀ p, m22F2 p ∈ m22H1F ↔ p ∈ m22H1F))
    ∧ (m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1) = 960)
    ∧ (m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
       ∀ p ∈ m22HexadL, σ p ∈ m22HexadL) = 192)
    ∧ (m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
       (∀ p : Fin 22, σ (m22F1 p) = m22F1 (σ p)) ∧ ∀ p : Fin 22, σ (m22F2 p) = m22F2 (σ p)) = 1) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, count_two_point, count_two_point_hexad,
    count_centralizer⟩

end CertificateChecks.KernelLC.Witt

end
