module

public import Certificates.Kernel.LocalComp.WittCount
public import Certificates.Kernel.LocalComp.WittK2030

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.KC.WCnt CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign

theorem mem_hexad0 : ∀ x : Fin 22, inM 655879 x.val = true ↔ x ∈ hexad0 := by decide +kernel
theorem list_hexad0 : ∀ x : Fin 22, x ∈ hexad0 ↔ x.val ∈ [0, 1, 2, 9, 17, 19] := by
  decide +kernel
theorem mem_hexadD0 : ∀ x : Fin 22, inM 1085496 x.val = true ↔ x ∈ hexadD0 := by decide +kernel
theorem list_hexadD0 : ∀ x : Fin 22, x ∈ hexadD0 ↔ x.val ∈ [3, 4, 5, 12, 15, 20] := by
  decide +kernel
theorem mem_hexadT0 : ∀ x : Fin 22, inM 1065035 x.val = true ↔ x ∈ hexadT0 := by decide +kernel
theorem list_hexadT0 : ∀ x : Fin 22, x ∈ hexadT0 ↔ x.val ∈ [0, 1, 3, 6, 14, 20] := by
  decide +kernel
theorem inter_hexadT0 : ∀ x : Fin 22, x ∈ hexad0 → x ∈ hexadT0 → inM 3 x.val = true := by
  decide +kernel

theorem fix012 {σ : Perm (Fin 22)} (h : ∀ x ∈ hexad0, (σ * 1) x = x) :
    Nat.beq (σ 0).val 0 = true ∧ Nat.beq (σ 1).val 1 = true ∧ Nat.beq (σ 2).val 2 = true := by
  simp only [mul_one] at h
  simp [h 0 (by decide), h 1 (by decide), h 2 (by decide)]

theorem count_kernel_hexad0 :
    m22Count (fun g => ∀ x ∈ hexad0, g x = x) = 16 :=
  (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun _ h => fix012 h).trans k2030a

theorem count_kernel_sq_hexad0 :
    m22Count (fun g => (∀ x ∈ hexad0, g x = x) ∧ ∀ x, g (g x) = x) = 16 :=
  (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun _ h => fix012 h.1).trans k2030b

theorem count_kernel_fix_hexad0 :
    m22Count (fun g => (∀ x ∈ hexad0, g x = x) ∧ g 3 = 3) = 1 :=
  (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun _ h => fix012 h.1).trans k2030c

theorem count_stabilizer_D0 :
    m22Count (fun g => (∀ x ∈ hexad0, g x ∈ hexad0) ∧ ∀ x ∈ hexadD0, g x ∈ hexadD0) = 360 := by
  refine (m22Count_eq_wcB _ _ (fun τ => ?_) 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k2030d
  · rw [Bool.eq_iff_iff, Bool.and_eq_true,
      presT_pkw τ hexad0 _ _ list_hexad0 (by decide) mem_hexad0,
      presT_pkw τ hexadD0 _ _ list_hexadD0 (by decide) mem_hexadD0,
      decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
  · simp only [mul_one] at h
    exact ⟨(mem_hexad0 _).2 (h.1 0 (by decide)), (mem_hexad0 _).2 (h.1 1 (by decide)),
      (mem_hexad0 _).2 (h.1 2 (by decide))⟩

theorem count_stabilizer_T0 :
    m22Count (fun g => (∀ x ∈ hexad0, g x ∈ hexad0) ∧ ∀ x ∈ hexadT0, g x ∈ hexadT0) = 96 := by
  refine (m22Count_eq_wcB _ _ (fun τ => ?_) 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k2030e
  · rw [Bool.eq_iff_iff, Bool.and_eq_true,
      presT_pkw τ hexad0 _ _ list_hexad0 (by decide) mem_hexad0,
      presT_pkw τ hexadT0 _ _ list_hexadT0 (by decide) mem_hexadT0,
      decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
  · simp only [mul_one] at h
    exact ⟨inter_hexadT0 _ (h.1 0 (by decide)) (h.2 0 (by decide)),
      inter_hexadT0 _ (h.1 1 (by decide)) (h.2 1 (by decide)),
      (mem_hexad0 _).2 (h.1 2 (by decide))⟩

theorem facts2030 :
    (m22Count (fun g => ∀ x ∈ hexad0, g x = x) = 16)
    ∧ (m22Count (fun g => (∀ x ∈ hexad0, g x = x) ∧ ∀ x, g (g x) = x) = 16)
    ∧ (m22Count (fun g => (∀ x ∈ hexad0, g x = x) ∧ g 3 = 3) = 1)
    ∧ (m22Count (fun g => (∀ x ∈ hexad0, g x ∈ hexad0) ∧ ∀ x ∈ hexadD0, g x ∈ hexadD0) = 360)
    ∧ (m22Count (fun g => (∀ x ∈ hexad0, g x ∈ hexad0) ∧ ∀ x ∈ hexadT0, g x ∈ hexadT0) = 96)
    ∧ (hexadD0 ∈ hexadList)
    ∧ (hexadT0 ∈ hexadList)
    ∧ ((hexad0 ∩ hexadD0).card = 0)
    ∧ ((hexad0 ∩ hexadT0).card = 2) :=
  ⟨count_kernel_hexad0, count_kernel_sq_hexad0, count_kernel_fix_hexad0, count_stabilizer_D0,
    count_stabilizer_T0, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

end CertificateChecks.KernelLC.Witt

end
