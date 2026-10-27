module

public import Certificates.Kernel.MonsterExist.P5.Table
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5

theorem sortFin_eq (T : Finset (Fin 81)) :
    sortFin T = (List.finRange 81).filter (fun x => decide (x ∈ T)) := by
  unfold sortFin
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact Finset.pairwise_sort T _
  · exact ((List.sortedLT_finRange 81).pairwise.filter _).imp le_of_lt
  · rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ((List.nodup_finRange 81).filter _)]
    intro x
    simp [Finset.mem_sort]

@[expose] noncomputable def bitN (E : Nat) (k : Fin 81) : Bool :=
  Nat.blt 0 (Nat.land E (Nat.shiftLeft 1 k.val))

theorem bitN_eq (E : Nat) (k : Fin 81) : bitN E k = E.testBit k.val := by
  unfold bitN
  have h : E &&& 1 <<< k.val = if E.testBit k.val then 2 ^ k.val else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow]
    split
    · rename_i hv
      rw [Nat.testBit_two_pow]
      by_cases hij : k.val = j
      · subst hij
        simp [hv]
      · simp [hij]
    · rename_i hv
      rw [Nat.zero_testBit]
      by_cases hij : k.val = j
      · subst hij
        simp [hv]
      · simp [hij]
  change Nat.blt 0 (E &&& 1 <<< k.val) = _
  rw [h]
  split
  · rename_i hv
    rw [hv]
    exact Nat.blt_eq.mpr (Nat.two_pow_pos _)
  · rename_i hv
    simp only [Bool.not_eq_true] at hv
    rw [hv]
    rfl

@[expose] noncomputable def extMask (l : List (Fin 81)) (x : Fin 81) : Nat :=
  l.foldr (fun s acc => Nat.lor acc (Nat.lor (Nat.shiftLeft 1 s.val)
    (Nat.lor (Nat.shiftLeft 1 (tbF x s).val) (Nat.shiftLeft 1 (tbF x (tbF x s)).val)))) 0

theorem testBit_extMask (l : List (Fin 81)) (x k : Fin 81) :
    (extMask l x).testBit k.val = true ↔ ∃ s ∈ l, s = k ∨ tbF x s = k ∨ tbF x (tbF x s) = k := by
  induction l with
  | nil => simp [extMask]
  | cons s l ih =>
    change ((extMask l x) ||| ((1 <<< s.val) ||| ((1 <<< (tbF x s).val) |||
      (1 <<< (tbF x (tbF x s)).val)))).testBit k.val = true ↔ _
    simp only [List.mem_cons, exists_eq_or_imp, Nat.testBit_or, Bool.or_eq_true, ih,
      Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq, Fin.val_inj]
    exact or_comm

@[expose] noncomputable def extList (l : List (Fin 81)) (x : Fin 81) : List (Fin 81) :=
  (List.finRange 81).filter (bitN (extMask l x))

theorem sortFin_extSet (l : List (Fin 81)) (x : Fin 81) :
    sortFin (extSet l.toFinset x) = extList l x := by
  rw [sortFin_eq, extList]
  congr 1
  funext k
  rw [bitN_eq]
  have h := testBit_extMask l x k
  have h' : k ∈ extSet l.toFinset x ↔ ∃ s ∈ l, s = k ∨ tbF x s = k ∨ tbF x (tbF x s) = k := by
    simp only [extSet, Finset.mem_union, Finset.mem_image, List.mem_toFinset, tb_eq_tbF]
    constructor
    · rintro ((h | ⟨s, hs, h⟩) | ⟨s, hs, h⟩)
      · exact ⟨k, h, Or.inl rfl⟩
      · exact ⟨s, hs, Or.inr (Or.inl h)⟩
      · exact ⟨s, hs, Or.inr (Or.inr h)⟩
    · rintro ⟨s, hs, h | h | h⟩
      · exact Or.inl (Or.inl (h ▸ hs))
      · exact Or.inl (Or.inr ⟨s, hs, h⟩)
      · exact Or.inr ⟨s, hs, h⟩
  by_cases hk : k ∈ extSet l.toFinset x
  · rw [decide_eq_true hk, (h.2 (h'.1 hk))]
  · rw [decide_eq_false hk]
    cases hb : (extMask l x).testBit k.val
    · rfl
    · exact absurd (h'.2 (h.1 hb)) hk

@[expose] noncomputable def closedM (T : List (Fin 81)) : Bool :=
  decide (T.length = 81) || T.all fun u => T.all fun v => T.contains (tbF u v)

theorem closedL_eq (T : List (Fin 81)) : closedL T = closedM T := by
  rw [closedL, closedM, tb_eq_tbF]

@[expose] noncomputable def checkLatM (L : List (List (Fin 81))) (l : List (Fin 81)) (x : Fin 81) : Bool :=
  l.contains x || (L.contains (extList l x) || !(closedM (extList l x)))

theorem checkLat_eq (l : List (Fin 81)) (x : Fin 81) : checkLat l x = checkLatM lattice l x := by
  rw [checkLat, checkLatM, sortFin_extSet, closedL_eq]
  cases l.contains x <;> cases closedM (extList l x) <;> cases lattice.contains (extList l x) <;> rfl

theorem latticeClosedB_eq :
    latticeClosedB = lattice.all fun l => (List.finRange 81).all (checkLatM lattice l) := by
  rw [latticeClosedB]
  congr 1
  funext l
  congr 1
  funext x
  exact checkLat_eq l x

end CertificateChecks.MonsterExist.P5

end
