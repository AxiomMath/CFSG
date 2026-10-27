module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsOverInputs
public import CFSG.Sporadic.Schreier.TitsBasic
public import Mathlib.Order.Atoms

public section

namespace CFSG.QuasithinUnique.Setup.X6.TitsLat

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2

section Words

variable {G : Type*} [Group G]

theorem wordIn_nil (k : ℕ) (gs : ℕ → G) : wordIn k gs [] = 1 := rfl

theorem wordIn_cons (k : ℕ) (gs : ℕ → G) (a : ℤ) (w : List ℤ) :
    wordIn k gs (a :: w) = wordIn k gs [a] * wordIn k gs w := by
  rw [← wordIn_append, List.singleton_append]

theorem wordIn_neg_single (k : ℕ) (gs : ℕ → G) (a : ℤ) :
    wordIn k gs [-a] = (wordIn k gs [a])⁻¹ := by
  by_cases h : a ≠ 0 ∧ a.natAbs ≤ k
  · have h' : -a ≠ 0 ∧ (-a).natAbs ≤ k := by
      rw [Int.natAbs_neg, neg_ne_zero]
      exact h
    simp only [wordIn, toLetters, List.filterMap_cons, List.filterMap_nil, dite_eq_left h, dite_eq_left h']
    rcases lt_or_gt_of_ne h.1 with hn | hp
    · have h1 : decide (0 < a) = false := decide_eq_false (by omega)
      have h2 : decide (a < 0) = true := decide_eq_true hn
      simp [h1, h2, Int.natAbs_neg]
    · have h1 : decide (0 < a) = true := decide_eq_true hp
      have h2 : decide (a < 0) = false := decide_eq_false (by omega)
      simp [h1, h2, Int.natAbs_neg]
  · have h' : ¬ (-a ≠ 0 ∧ (-a).natAbs ≤ k) := by
      rw [Int.natAbs_neg, neg_ne_zero]
      exact h
    simp only [wordIn, toLetters, List.filterMap_cons, List.filterMap_nil, dite_eq_right h, dite_eq_right h']
    simp

theorem wordIn_titsInvWord (k : ℕ) (gs : ℕ → G) :
    ∀ w : List ℤ, wordIn k gs (titsInvWord w) = (wordIn k gs w)⁻¹
  | [] => by rw [titsInvWord, List.map_nil, List.reverse_nil, wordIn_nil, inv_one]
  | a :: w => by
    have e : titsInvWord (a :: w) = titsInvWord w ++ [-a] := by
      simp [titsInvWord]
    rw [e, wordIn_append, wordIn_titsInvWord k gs w, wordIn_neg_single, wordIn_cons k gs a w,
      mul_inv_rev]

theorem wordIn_flatMap_mem {k : ℕ} {gs : ℕ → G} {K : Subgroup G} (piece : ℕ → List ℤ) :
    ∀ L : List ℕ, (∀ c ∈ L, wordIn k gs (piece c) ∈ K) → wordIn k gs (L.flatMap piece) ∈ K
  | [], _ => by
    rw [List.flatMap_nil, wordIn_nil]
    exact K.one_mem
  | c :: L, h => by
    rw [List.flatMap_cons, wordIn_append]
    exact K.mul_mem (h c List.mem_cons_self)
      (wordIn_flatMap_mem piece L fun d hd => h d (List.mem_cons_of_mem c hd))

end Words

theorem eq_top_of_prime_index {G : Type*} [Group G] {S H M : Subgroup G} (hH : IsCoatom H)
    (hSH : S ≤ H) (hSM : S ≤ M) (hp : (S.subgroupOf H).index.Prime) {z g : G} (hzM : z ∈ M)
    (hzH : z ∈ H) (hzS : z ∉ S) (hgM : g ∈ M) (hgH : g ∉ H) : M = ⊤ := by
  have h1 : S ≤ M ⊓ H := le_inf hSM hSH
  have h2 : M ⊓ H ≤ H := inf_le_right
  have hmul := Subgroup.relIndex_mul_relIndex S (M ⊓ H) H h1 h2
  have hp' : (S.relIndex H).Prime := hp
  rw [← hmul, Nat.prime_mul_iff] at hp'
  rcases hp' with ⟨-, h⟩ | ⟨-, h⟩
  · have hle : H ≤ M := fun x hx => (Subgroup.relIndex_eq_one.1 h hx).1
    refine hH.2 M (lt_of_le_of_ne hle fun e => hgH ?_)
    rw [e]
    exact hgM
  · exact absurd (Subgroup.relIndex_eq_one.1 h ⟨hzM, hzH⟩) hzS

end CFSG.QuasithinUnique.Setup.X6.TitsLat
