module

public import Certificates.Data.Kernel.M24G.Lists
public import CFSG.Certificates.Kernel.Common.SliceGlue

public section

namespace CFSG.KC.M24G

open CFSG.KC

theorem allIdx_append {α : Type} (g : Nat → α → Bool) :
    ∀ (A B : List α) (i : Nat), allIdx g (A ++ B) i = (allIdx g A i && allIdx g B (i + A.length))
  | [], B, i => by simp [allIdx]
  | x :: A, B, i => by
    rw [List.cons_append, allIdx, allIdx, allIdx_append g A B (i + 1), Bool.and_assoc,
      List.length_cons, Nat.add_assoc, Nat.add_comm 1]

theorem allIdx_of_slices {α : Type} (g : Nat → α → Bool) (b m : Nat) (L : List α) (i : Nat)
    (hL : L.length = m * b) (h : ∀ j < m, allIdx g (SliceGlue.slice L (j * b) b) (i + j * b) = true) :
    allIdx g L i = true := by
  have key : ∀ j, j ≤ m → allIdx g (L.take (j * b)) i = true := by
    intro j
    induction j with
    | zero => intro _; simp [allIdx]
    | succ j ih =>
      intro hj
      have hle : j * b ≤ L.length := by rw [hL]; exact Nat.mul_le_mul_right b (by omega)
      rw [Nat.succ_mul, List.take_add, allIdx_append, ih (by omega), Bool.true_and,
        List.length_take, Nat.min_eq_left hle]
      exact h j (by omega)
  have := key m (Nat.le_refl m)
  rwa [List.take_of_length_le (by rw [hL]; exact Nat.le_refl _)] at this

end CFSG.KC.M24G

end
