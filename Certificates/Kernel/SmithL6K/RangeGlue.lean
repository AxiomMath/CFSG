module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Data.Kernel.SmithL6KS

public section

namespace CFSG.SmithL6.K

theorem drop_drop_add {α : Type} (l : List α) (a n : Nat) : (l.drop a).drop n = l.drop (a + n) := by
  simp [List.drop_drop, Nat.add_comm]

theorem pinMapR_add {β α : Type} [BEq α] [LawfulBEq α] (f : β → α) (src : List β) (dst : List α)
    (a n m : Nat) (h1 : pinMapR f src dst a n = true) (h2 : pinMapR f src dst (a + n) m = true) :
    pinMapR f src dst a (n + m) = true := by
  unfold pinMapR at h1 h2 ⊢
  rw [beq_iff_eq] at h1 h2 ⊢
  rw [List.take_add, List.take_add, List.map_append, drop_drop_add, drop_drop_add, h1, h2]

theorem pinMapR_chunks {β α : Type} [BEq α] [LawfulBEq α] (f : β → α) (src : List β)
    (dst : List α) (lo m : Nat) : ∀ k : Nat, (∀ q < k, pinMapR f src dst (lo + q * m) m = true) →
    pinMapR f src dst lo (k * m) = true
  | 0, _ => by simp [pinMapR]
  | k + 1, h => by
    rw [Nat.add_mul, Nat.one_mul]
    exact pinMapR_add f src dst lo (k * m) m
      (pinMapR_chunks f src dst lo m k fun q hq => h q (by omega)) (h k (by omega))

theorem pinMapR_of_chunks {β α : Type} [BEq α] [LawfulBEq α] (f : β → α) (src : List β)
    (dst : List α) (lo k m n : Nat) (hn : k * m = n)
    (h : ∀ q < k, pinMapR f src dst (lo + q * m) m = true) : pinMapR f src dst lo n = true := by
  subst hn
  exact pinMapR_chunks f src dst lo m k h

theorem sRowsK_add (C : List Nat) (L : List (List Nat)) (W lo a b : Nat) :
    sRowsK C L W lo (a + b) = (sRowsK C L W lo a && sRowsK C L W (lo + a) b) := by
  unfold sRowsK
  rw [List.take_add, List.all_append, drop_drop_add]

theorem sRowsK_chunks (C : List Nat) (L : List (List Nat)) (W lo m : Nat) :
    ∀ k : Nat, (∀ q < k, sRowsK C L W (lo + q * m) m = true) → sRowsK C L W lo (k * m) = true
  | 0, _ => by simp [sRowsK]
  | k + 1, h => by
    rw [Nat.add_mul, Nat.one_mul, sRowsK_add, sRowsK_chunks C L W lo m k (fun q hq => h q (by omega)),
      h k (by omega)]
    all_goals rfl

theorem sRowsK_of_chunks (C : List Nat) (L : List (List Nat)) (W lo k m n : Nat) (hn : k * m = n)
    (h : ∀ q < k, sRowsK C L W (lo + q * m) m = true) : sRowsK C L W lo n = true := by
  subst hn
  exact sRowsK_chunks C L W lo m k h

end CFSG.SmithL6.K

end
