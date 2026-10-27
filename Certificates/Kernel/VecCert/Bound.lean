module

public import CFSG.Sporadic.Bridge.TwoGen

public section

namespace CertificateChecks.KernelVec

open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen TauCeti

theorem card_le_of_rels {G : Type*} [Group G] (P : GroupPresentation) (hP : P.generatorCount = 2)
    {x y : G} (hclosure : Subgroup.closure ({x, y} : Set G) = ⊤)
    (hrel : ∀ v ∈ P.relatorLetters, wordProd (img2 x y) v = 1) [Finite P.Group] {k : ℕ}
    (hcard : Nat.card P.Group ≤ k) : Nat.card G ≤ k := by
  have hsurj : Function.Surjective (presHom P (img2 x y) hrel) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hclosure, Subgroup.closure_le]
    rintro g (h | h)
    · exact ⟨presGen P 0, by
        rw [presHom_presGen P (img2 x y) hrel (by omega), h]
        simp [img2]⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨presGen P 1, by
        rw [presHom_presGen P (img2 x y) hrel (by omega), h]
        simp [img2]⟩
  exact (Nat.card_le_card_of_surjective _ hsurj).trans hcard

end CertificateChecks.KernelVec

end
