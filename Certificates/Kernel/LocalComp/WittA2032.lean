module

public import Certificates.Kernel.LocalComp.WittCount
public import Certificates.Kernel.LocalComp.WittWords
public import Certificates.Kernel.LocalComp.WittK2032

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.KC.WCnt CFSG.KS.PCnt CFSG.ComponentClassification.WittDesign

theorem pt_tA : ∀ i : Fin 22, pt tA i.val = (aFun i).val := by decide +kernel
theorem fix_aFun : ∀ y : Fin 22, aFun y = y → inM 1982480 y.val = true := by decide +kernel

theorem count_aFun : m22Count (fun g => ∀ x, g x = aFun x) = 1 := by
  refine (m22Count_eq_wc _ 1 (Subgroup.one_mem _) _ KernelSpor.M22Syl.pk_one _ _ _
    fun σ h => ?_).trans k2032a
  simp only [mul_one] at h
  simp only [h]
  exact ⟨rfl, rfl, rfl⟩

theorem count_centralizer_a :
    m22Count (fun g => ∀ x, g (aFun x) = aFun (g x)) = 384 := by
  refine (m22Count_eq_wcB (fun g => ∀ x, g (aFun x) = aFun (g x)) (relT tA tA)
    (fun τ => relT_pkw τ aFun aFun tA tA pt_tA pt_tA)
    (wordPerm wB) (wordPerm_mem _) _ pk_wB _ _ _ fun σ h => ?_).trans k2032b
  have hfix : ∀ e : Fin 22, aFun e = e → inM 1982480 ((σ * wordPerm wB) e).val = true :=
    fun e he => fix_aFun _ (by rw [← h e, he])
  rw [← mul_apply_of_pk pk_wB σ (e := 4) rfl, ← mul_apply_of_pk pk_wB σ (e := 14) rfl,
    ← mul_apply_of_pk pk_wB σ (e := 17) rfl]
  exact ⟨hfix 4 rfl, hfix 14 rfl, hfix 17 rfl⟩

theorem facts2032 :
    (m22Count (fun g => ∀ x, g x = aFun x) = 1)
    ∧ (m22Count (fun g => ∀ x, g (aFun x) = aFun (g x)) = 384)
    ∧ ((∀ x, aFun (aFun x) = x) ∧ aFun 0 ≠ 0) :=
  ⟨count_aFun, count_centralizer_a, by decide +kernel⟩

end CertificateChecks.KernelLC.Witt

end
