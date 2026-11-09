module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Group.Nat.Range
public import Mathlib.Order.Interval.Finset.Nat

public section

namespace CFSG.KD.StdOdd.Cent

theorem cens_perm{α : Type*} {n : ℕ} (pt pt' : ℕ → α) (τ : ℕ → ℕ) (P : α → Prop)
    [DecidablePred P] (hτ : ∀ i < n, τ i < n) (hinj : ∀ i < n, ∀ j < n, τ i = τ j → i = j)
    (hpt : ∀ i < n, pt' i = pt (τ i)) :
    ((Finset.range n).filter fun i => P (pt' i)).card =
      ((Finset.range n).filter fun i => P (pt i)).card := by
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n) (t := Finset.range n)
    (fun i _ => τ i) (fun i hi => Finset.mem_range.2 (hτ i (Finset.mem_range.1 hi)))
    (fun i j hi hj h => hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) h) le_rfl
  refine Finset.card_bij (fun i _ => τ i) ?_ ?_ ?_
  · intro i hi
    obtain ⟨hi1, hPi⟩ := Finset.mem_filter.1 hi
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (hτ i (Finset.mem_range.1 hi1)), ?_⟩
    rwa [← hpt i (Finset.mem_range.1 hi1)]
  · intro i hi j hj h
    exact hinj i (Finset.mem_range.1 (Finset.mem_filter.1 hi).1) j
      (Finset.mem_range.1 (Finset.mem_filter.1 hj).1) h
  · intro j hj
    obtain ⟨hj1, hPj⟩ := Finset.mem_filter.1 hj
    obtain ⟨i, hi, e⟩ := hsurj j hj1
    refine ⟨i, Finset.mem_filter.2 ⟨hi, ?_⟩, e.symm⟩
    rw [hpt i (Finset.mem_range.1 hi), ← e]
    exact hPj

theorem cens_iterate_iff {α : Type*} {f : α → α} {P : α → Prop} (hP : ∀ u, (P (f u) ↔ P u)) :
    ∀ (k : ℕ) (u : α), P (f^[k] u) ↔ P u
  | 0, _ => Iff.rfl
  | k + 1, u => by
    rw [Function.iterate_succ_apply']
    exact (hP _).trans (cens_iterate_iff hP k u)

theorem cens_blocks{α : Type*} {p m : ℕ} (pt : ℕ → α) (f : α → α) (P : α → Prop)
    [DecidablePred P] (hP : ∀ u, (P (f u) ↔ P u))
    (hblk : ∀ k < p, ∀ j < m, pt (k * m + j) = f^[k] (pt j)) :
    ((Finset.range (p * m)).filter fun i => P (pt i)).card =
      p * ((Finset.range m).filter fun i => P (pt i)).card := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Nat.succ_mul, Finset.range_add_eq_union, Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.disjoint_range_addLeftEmbedding _ _)),
      ih fun k hk j hj => hblk k (by omega) j hj, Nat.succ_mul, Finset.filter_map,
      Finset.card_map]
    congr 2
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Function.comp_apply, addLeftEmbedding_apply]
    refine and_congr_right fun hj => ?_
    rw [hblk p (by omega) j hj]
    exact cens_iterate_iff hP p (pt j)

end CFSG.KD.StdOdd.Cent

end
