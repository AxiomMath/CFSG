module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFacts
public import CFSG.Monster.Existence.StdOdd.Cert.Lie
public import CFSG.Monster.Existence.StdOdd.Cert.Sylow57

public section

namespace CFSG.KD.StdOdd.Cent

open Matrix CFSG.Monster.Existence.StdOdd.Cert

theorem rhoC_wM (w : List (ℕ × Bool)) (u v : Pt) :
    rhoC (wM w *ᵥ u) (wM w *ᵥ v) = rhoC u v := by
  have e : ∀ x : Pt, wM w *ᵥ x = repOf w • x := fun x => by
    change _ = rgrpMat (repOf w) *ᵥ x
    rw [rgrpMat_repOf]
    rfl
  have hr : ∀ a b : Pt, rhoC a b =
      if a = b then 0 else if formPt a b ≠ 0 then 4 else if brPt a b ≠ 0 then 3 else 5 := by
    intro a b
    rw [rhoC, formPt_eq, brPt_eq]
    rfl
  rw [e, e, hr, hr]
  simp only [(MulAction.injective (repOf w)).eq_iff, formPt_smul, brPt_smul, ne_eq,
    smul_eq_zero_iff_eq]

theorem prof_wM (xw : List (ℕ × Bool)) (K1 : List (ℕ × ℕ)) (u : Pt) :
    (∀ q ∈ K1, rhoC (wM xw *ᵥ u) (wM xw ^ q.1 *ᵥ (wM xw *ᵥ u)) = q.2) ↔
      ∀ q ∈ K1, rhoC u (wM xw ^ q.1 *ᵥ u) = q.2 := by
  have h : ∀ k, rhoC (wM xw *ᵥ u) (wM xw ^ k *ᵥ (wM xw *ᵥ u)) = rhoC u (wM xw ^ k *ᵥ u) := by
    intro k
    rw [mulVec_mulVec, ← pow_succ, pow_succ', ← mulVec_mulVec, rhoC_wM]
  simp only [h]

end CFSG.KD.StdOdd.Cent

end
