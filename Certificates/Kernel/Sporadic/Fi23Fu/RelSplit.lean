module

public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KD.Fi23Fu

open CFSG.KC.Ord

section
variable {RB : Nat → Nat} {mul : Nat → Nat → Nat} {ONE L : Nat}

theorem strictN_eqF (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem andB_ble_blt (lo i hi : Nat) :
    andB (Nat.ble lo i) (Nat.blt i hi) = decide (lo ≤ i ∧ i < hi) := by
  have e1 : Nat.ble lo i = decide (lo ≤ i) := Bool.eq_iff_iff.2 (by simp [Nat.ble_eq])
  have e2 : Nat.blt i hi = decide (i < hi) := Bool.eq_iff_iff.2 (by simp [Nat.blt_eq])
  rw [e1, e2]
  unfold andB
  by_cases a : lo ≤ i <;> by_cases b : i < hi <;> simp [a, b]

@[expose] noncomputable def segStep (RB : Nat → Nat) (mul : Nat → Nat → Nat) (ONE L lo hi i : Nat)
    (x : Nat × Bool) (acc : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) acc
    ((fun m => Bool.rec (motive := fun _ => Nat) (mul acc m) m (Nat.beq acc ONE)) (letM RB L x))
    (andB (Nat.ble lo i) (Nat.blt i hi))

theorem segProd_cons (lo hi : Nat) (x : Nat × Bool) (l : List (Nat × Bool)) (i acc : Nat) :
    segProd RB mul ONE L lo hi (x :: l) i acc =
      segProd RB mul ONE L lo hi l (i + 1) (segStep RB mul ONE L lo hi i x acc) :=
  strictN_eqF _ _

theorem segStep_out {lo hi i : Nat} (h : ¬(lo ≤ i ∧ i < hi)) (x : Nat × Bool) (acc : Nat) :
    segStep RB mul ONE L lo hi i x acc = acc := by
  unfold segStep
  rw [andB_ble_blt, decide_eq_false h]

theorem segStep_congr {lo hi lo' hi' i : Nat} (h : (lo ≤ i ∧ i < hi) ↔ (lo' ≤ i ∧ i < hi'))
    (x : Nat × Bool) (acc : Nat) :
    segStep RB mul ONE L lo hi i x acc = segStep RB mul ONE L lo' hi' i x acc := by
  unfold segStep
  rw [andB_ble_blt, andB_ble_blt]
  simp only [decide_eq_decide.2 h]

theorem segProd_id {lo mid : Nat} : ∀ (l : List (Nat × Bool)) (i acc : Nat), mid ≤ i →
    segProd RB mul ONE L lo mid l i acc = acc
  | [], _, _, _ => rfl
  | x :: l, i, acc, h => by
    rw [segProd_cons, segStep_out (by omega), segProd_id l (i + 1) acc (by omega)]

theorem segProd_shift {lo mid hi : Nat} (h1 : lo ≤ mid) : ∀ (l : List (Nat × Bool)) (i acc : Nat),
    mid ≤ i → segProd RB mul ONE L lo hi l i acc = segProd RB mul ONE L mid hi l i acc
  | [], _, _, _ => rfl
  | x :: l, i, acc, h => by
    rw [segProd_cons, segProd_cons, segStep_congr (lo' := mid) (hi' := hi) (by omega),
      segProd_shift h1 l (i + 1) _ (by omega)]

theorem segProd_comp {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    ∀ (l : List (Nat × Bool)) (i acc : Nat),
      segProd RB mul ONE L lo hi l i acc =
        segProd RB mul ONE L mid hi l i (segProd RB mul ONE L lo mid l i acc)
  | [], _, _ => rfl
  | x :: l, i, acc => by
    by_cases hi' : i < mid
    · rw [segProd_cons, segProd_cons (lo := lo) (hi := mid), segProd_cons (lo := mid) (hi := hi),
        segStep_congr (lo' := lo) (hi' := mid) (by omega),
        segStep_out (lo := mid) (hi := hi) (by omega), segProd_comp h1 h2 l (i + 1)]
    · rw [segProd_id (lo := lo) (mid := mid) (x :: l) i acc (by omega),
        segProd_shift (lo := lo) (mid := mid) (hi := hi) h1 (x :: l) i acc (by omega)]

theorem relOK_split {rels : List (List (Nat × Bool))} {r : Nat} (m V : Nat)
    (hr : Nat.blt r (lenL rels) = true) (h0 : Nat.blt (nat_lit 0) (lenL (nthRel rels r)) = true)
    (hm : Nat.ble m (lenL (nthRel rels r)) = true)
    (p1 : Nat.beq (segProd RB mul ONE L (nat_lit 0) m (nthRel rels r) (nat_lit 0) ONE) V = true)
    (p2 : Nat.beq (segProd RB mul ONE L m (lenL (nthRel rels r)) (nthRel rels r) (nat_lit 0) V) ONE =
      true) :
    relOK RB mul rels L ONE r = true := by
  unfold relOK relSegOK
  dsimp only
  rw [segProd_comp (Nat.zero_le m) (Nat.le_of_ble_eq_true hm), Nat.eq_of_beq_eq_true p1, p2, hr, h0,
    Nat.ble_eq_true_of_le (Nat.le_refl _)]
  rfl
end

end CFSG.KD.Fi23Fu

end
