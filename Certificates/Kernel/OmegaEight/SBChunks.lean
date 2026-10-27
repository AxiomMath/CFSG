module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.ToDual

public section

namespace CertificateChecks.KernelO8

@[expose] def chunks {α : Type} (n : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | k + 1, L => L.take n :: chunks n k (L.drop n)

theorem chunks_flatten {α : Type} (n : ℕ) :
    ∀ (k : ℕ) (L : List α), L.length ≤ n * k → (chunks n k L).flatten = L
  | 0, L, h => by simp_all [chunks]
  | k + 1, L, h => by
    rw [chunks, List.flatten_cons, chunks_flatten n k (L.drop n)
      (by rw [List.length_drop]; rw [Nat.mul_succ] at h; omega), List.take_append_drop]

theorem chunks_length {α : Type} (n k : ℕ) (L : List α) : (chunks n k L).length = k := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih => rw [chunks, List.length_cons, ih]

theorem foldl_range_chain {β : Type} (f : β → ℕ → β) (acc : ℕ → β) (k : ℕ)
    (h : ∀ s < k, f (acc s) s = acc (s + 1)) : (List.range k).foldl f (acc 0) = acc k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih fun s hs => h s (by omega), List.foldl_cons,
      List.foldl_nil, h k (by omega)]

theorem range_mul_eq_flatMap (n k : ℕ) :
    List.range (n * k) = (List.range k).flatMap fun s => List.range' (n * s) n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, List.range_add, ih, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.range'_eq_map_range]

theorem foldl_range_blocks {β : Type} (f : β → ℕ → β) (n k : ℕ) (b : β) :
    (List.range (n * k)).foldl f b =
      (List.range k).foldl (fun acc s => (List.range' (n * s) n).foldl f acc) b := by
  rw [range_mul_eq_flatMap, List.foldl_flatMap]

end CertificateChecks.KernelO8

end
