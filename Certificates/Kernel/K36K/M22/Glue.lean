module

public import Certificates.Kernel.K36K.M22.Checks
public import CFSG.Certificates.Kernel.K36K.Planes

public section

namespace CertificateChecks.KernelK36K.M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.MaxD2 CFSG.KD.K36K CFSG.Blueprint
  CFSG.ComponentClassification.PSL3Four CFSG.LocalAnalysis.UniquenessCase.UCK.Spor
  Certificates.K36Spor

theorem tab0 : TabRep (unpack 22 5 (GP 0)) (List.formPerm [0, 12] * List.formPerm [1, 7] *
    List.formPerm [2, 15] * List.formPerm [3, 11] * List.formPerm [5, 21] * List.formPerm [6, 16] *
    List.formPerm [8, 9] * List.formPerm [10, 13] : Equiv.Perm (Fin 22)) :=
  ⟨size_u _, fun x => by
    rw [get_u x.2]
    revert x
    decide +kernel⟩

theorem tab1 : TabRep (unpack 22 5 (GP 1)) (List.formPerm [0, 21, 2, 20] *
    List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] * List.formPerm [5, 10, 6, 14] *
    List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18] : Equiv.Perm (Fin 22)) :=
  ⟨size_u _, fun x => by
    rw [get_u x.2]
    revert x
    decide +kernel⟩

theorem planes_M22 : ∃ E : Subgroup ↥NativeSporadic.M22, Nat.card E = 9 ∧
    ∀ A : Subgroup ↥NativeSporadic.M22, A ≤ E → CFSG.Open.IsElemAbelian 3 A → Nat.card A = 9 →
      Subgroup.closure (centSet A) = ⊤ := by
  obtain ⟨E, hEc, hEG, hE⟩ := planes_two k_sz k_gens k_cen (by decide) k_v k_cent k_words
    ⟨0, by decide, rfl⟩ Nat.prime_three tab0 tab1
  obtain ⟨E', hE'c, hE'⟩ := closure_centSet_eq_top (G := NativeSporadic.M22) rfl
    ⟨E, hEc, hEG, fun A hAE _ hAc => hE A hAE hAc⟩
  exact ⟨E', hE'c.trans (by decide), fun A hAE hAe hAc =>
    hE' A hAE hAe (hAc.trans (by decide))⟩

end CertificateChecks.KernelK36K.M22

end
