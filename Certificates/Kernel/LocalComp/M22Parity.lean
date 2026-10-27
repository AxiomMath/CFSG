module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count

public section

namespace CertificateChecks.KernelLC

open Equiv Equiv.Perm CFSG.ComponentClassification.WittDesign

theorem m22_le_alt : CFSG.Blueprint.NativeSporadic.M22 ≤ alternatingGroup (Fin 22) := by
  rw [CFSG.Blueprint.NativeSporadic.M22, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl <;>
  · rw [SetLike.mem_coe, mem_alternatingGroup]
    simp [List.formPerm_cons_cons]

theorem sign_of_fpf_invol {σ : Perm (Fin 22)} (h2 : ∀ x, σ (σ x) = x) (hf : ∀ x, σ x ≠ x) :
    sign σ = -1 := by
  have hne : σ ≠ 1 := fun h => hf 0 (by rw [h]; rfl)
  have hsq : σ ^ 2 = 1 := by
    ext x
    simp [pow_two, h2]
  have hord : orderOf σ = 2 := orderOf_eq_prime hsq hne
  obtain ⟨n, hn⟩ := cycleType_prime_order (hord ▸ Nat.prime_two)
  have hsupp : σ.support = Finset.univ := by
    ext x
    simp [hf x]
  have hsum := sum_cycleType σ
  rw [hn, hsupp, Finset.card_univ, Fintype.card_fin, hord, Multiset.sum_replicate,
    smul_eq_mul] at hsum
  have : n + 1 = 11 := by omega
  rw [sign_of_cycleType, hn, hord, Multiset.sum_replicate, Multiset.card_replicate, this]
  decide

theorem m22Count_fpf_invol :
    m22Count (fun g => (∀ x, g (g x) = x) ∧ ∀ x, g x ≠ x) = 0 := by
  rw [← card_m22_subtype, Nat.card_eq_zero]
  left
  refine ⟨fun ⟨g, h2, hf⟩ => ?_⟩
  have h1 := mem_alternatingGroup.mp (m22_le_alt g.2)
  rw [sign_of_fpf_invol h2 hf] at h1
  exact absurd h1 (by decide)

end CertificateChecks.KernelLC

end
