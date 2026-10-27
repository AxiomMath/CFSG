
module

public import Certificates.Kernel.Misc.E6StdBlow

public section

namespace CFSG.KC.Misc.E6Std

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.LieType.Chevalley.C2E6Std.MatrixModel
open CFSG.LieType.Chevalley.C2E6Std.MatrixModel.Native (code maskOf)

attribute [local irreducible] mulB powB oneB rowStarts fullRow

theorem bit_eq (x k : ℕ) : bit x k = (x.testBit k).toNat := by
  unfold bit
  rw [Nat.toNat_testBit]
  change (x >>> k) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem testBit_toNat_mul (b : Bool) (v k : ℕ) : (b.toNat * v).testBit k = (b && v.testBit k) := by
  cases b <;> simp

theorem testBit_toNat (b : Bool) (k : ℕ) : b.toNat.testBit k = (b && decide (k = 0)) := by
  cases b
  · simp
  · rw [Bool.toNat_true, testBit_one]
    simp

theorem testBit_toNat_shiftLeft (b : Bool) (q p : ℕ) :
    (Nat.shiftLeft b.toNat q).testBit p = (b && decide (p = q)) := by
  change (b.toNat <<< q).testBit p = _
  rw [Nat.testBit_shiftLeft, testBit_toNat]
  cases b
  · simp
  · by_cases h : p = q
    · simp [h]
    · by_cases h' : p ≥ q
      · have : p - q ≠ 0 := by omega
        simp [h, this]
      · simp [h, h']

theorem toNat_xor (a b : Bool) : Nat.xor a.toNat b.toNat = (xor a b).toNat := by
  cases a <;> cases b <;> rfl

theorem testBit_of_lt78 {v k : ℕ} (hv : v < 2 ^ 78) (hk : 78 ≤ k) : v.testBit k = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hk))

theorem testBit_vsmulK (b₀ b₁ : Bool) {v : ℕ} (hv : v < 2 ^ 78) (k : ℕ) (hk : k < 78) :
    (vsmulK b₀.toNat b₁.toNat v).testBit k = (b₀ && v.testBit k) ∧
      (vsmulK b₀.toNat b₁.toNat v).testBit (k + 78) = (b₁ && v.testBit k) := by
  have hx : Nat.land v (Nat.sub (Nat.shiftLeft 1 78) 1) = v := by
    change v &&& (2 ^ 78 - 1) = v
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hv]
  have hy : Nat.shiftRight v 78 = 0 := by
    change v >>> 78 = 0
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hv]
  unfold vsmulK
  rw [letN_eq, hx, letN_eq, hy]
  change ((b₀.toNat * v ^^^ b₁.toNat * 0) |||
    ((b₀.toNat * 0 ^^^ b₁.toNat * (v ^^^ 0)) <<< 78)).testBit k = _ ∧
    ((b₀.toNat * v ^^^ b₁.toNat * 0) |||
    ((b₀.toNat * 0 ^^^ b₁.toNat * (v ^^^ 0)) <<< 78)).testBit (k + 78) = _
  simp only [Nat.mul_zero, Nat.xor_zero, Nat.zero_xor, Nat.testBit_or, Nat.testBit_shiftLeft,
    testBit_toNat_mul]
  refine ⟨?_, ?_⟩
  · have : ¬ k ≥ 78 := by omega
    simp [this]
  · rw [testBit_of_lt78 hv (by omega)]
    simp

theorem maskOfK_eq (e : ℕ) : maskOfK e = maskOf e := by
  unfold maskOfK maskOf
  by_cases h : e < 64
  · have : Nat.blt e 64 = true := by
      rw [Nat.blt_eq]
      exact h
    rw [this]
    simp only [h, ↓reduceIte]
  · have : Nat.blt e 64 = false := by
      cases h' : Nat.blt e 64
      · rfl
      · rw [Nat.blt_eq] at h'
        exact absurd h' h
    rw [this]
    simp only [h, ↓reduceIte]
    rfl

theorem codeK_eq (codes a b : ℕ) : codeK codes a b = code codes a b := by
  unfold codeK code
  change (codes >>> (8 * (78 * a + b))) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem maskOf_lt {e : ℕ} (he : e < 136) : maskOf e < 2 ^ 78 := by
  unfold maskOf
  split_ifs with h
  · exact lt_trans h (by norm_num)
  · rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem testBit_ite_zero (c : Bool) (m k : ℕ) : (if c = true then m else 0).testBit k =
    (c && m.testBit k) := by
  cases c <;> simp

theorem testBit_rootColK (codes bits r l : ℕ) (b₀ b₁ : Bool) (hr : r < 78) (hl78 : l < 78)
    (hc : code codes r l < 136) (k : ℕ) (hk : k < 78) :
    (rootColK codes bits r b₀.toNat b₁.toNat l).testBit k =
        (Native.rootCol codes bits r b₀ b₁ l).1.testBit k ∧
      (rootColK codes bits r b₀.toNat b₁.toNat l).testBit (k + 78) =
        (Native.rootCol codes bits r b₀ b₁ l).2.testBit k := by
  have hm := maskOf_lt hc
  have hr' : 2 ^ r < 2 ^ 78 := Nat.pow_lt_pow_right (by norm_num) hr
  obtain ⟨m1, m2⟩ := testBit_vsmulK b₀ b₁ hm k hk
  obtain ⟨r1, r2⟩ := testBit_vsmulK (xor b₀ b₁) b₁ hr' k hk
  have hl : ∀ q, (2 ^ l).testBit q = decide (q = l) := by
    intro q
    rw [Nat.testBit_two_pow]
    by_cases h : q = l
    · simp [h]
    · simp [h, Ne.symm h]
  have hrr : ∀ q, (2 ^ r).testBit q = decide (q = r) := by
    intro q
    rw [Nat.testBit_two_pow]
    by_cases h : q = r
    · simp [h]
    · simp [h, Ne.symm h]
  unfold rootColK
  rw [maskOfK_eq, codeK_eq, bit_eq, toNat_xor, shl_one, shl_one]
  unfold Native.rootCol Native.vadd Native.vsmul Native.fbit
  simp only [Nat.one_shiftLeft]
  change ((2 ^ l ^^^ vsmulK b₀.toNat b₁.toNat (maskOf (code codes r l))) ^^^
      (bits.testBit (78 * r + l)).toNat * vsmulK (xor b₀ b₁).toNat b₁.toNat (2 ^ r)).testBit k
      = _ ∧ ((2 ^ l ^^^ vsmulK b₀.toNat b₁.toNat (maskOf (code codes r l))) ^^^
      (bits.testBit (78 * r + l)).toNat * vsmulK (xor b₀ b₁).toNat b₁.toNat
        (2 ^ r)).testBit (k + 78) = _
  simp only [Nat.testBit_xor, testBit_toNat_mul, m1, m2, r1, r2, hl]
  have hkl : decide (k + 78 = l) = false := by
    simp only [decide_eq_false_iff_not]
    omega
  rw [hkl]
  cases hf : bits.testBit (78 * r + l) <;> cases b₀ <;> cases b₁ <;>
    simp [hrr]

@[expose] noncomputable def blk4 (l v k : ℕ) : ℕ :=
  Nat.lor (Nat.lor (Nat.shiftLeft (bit v k) (Nat.add (Nat.mul 312 k) (Nat.mul 2 l)))
    (Nat.shiftLeft (bit v (Nat.add k 78)) (Nat.add (Nat.mul 312 k) (Nat.add (Nat.mul 2 l) 1))))
    (Nat.lor (Nat.shiftLeft (bit v (Nat.add k 78)) (Nat.add (Nat.add (Nat.mul 312 k) 156) (Nat.mul 2 l)))
      (Nat.shiftLeft (Nat.xor (bit v k) (bit v (Nat.add k 78)))
        (Nat.add (Nat.add (Nat.mul 312 k) 156) (Nat.add (Nat.mul 2 l) 1))))

theorem blowCol_step (l v k acc : ℕ) :
    letN (bit v k) (fun x₀ => letN (bit v (Nat.add k 78)) fun x₁ =>
      Bool.rec (motive := fun _ => Nat)
        (Nat.lor (Nat.lor acc (Nat.lor
          (Nat.shiftLeft x₀ (Nat.add (Nat.mul (nat_lit 312) k) (Nat.mul 2 l)))
          (Nat.shiftLeft x₁ (Nat.add (Nat.mul (nat_lit 312) k) (Nat.add (Nat.mul 2 l) 1)))))
          (Nat.lor
            (Nat.shiftLeft x₁ (Nat.add (Nat.add (Nat.mul (nat_lit 312) k) 156) (Nat.mul 2 l)))
            (Nat.shiftLeft (Nat.xor x₀ x₁)
              (Nat.add (Nat.add (Nat.mul (nat_lit 312) k) 156) (Nat.add (Nat.mul 2 l) 1)))))
        acc (Nat.beq (Nat.lor x₀ x₁) 0)) = Nat.lor acc (blk4 l v k) := by
  rw [letN_eq, letN_eq]
  cases h : Nat.beq (Nat.lor (bit v k) (bit v (Nat.add k 78))) 0
  · change (acc ||| _) ||| _ = acc ||| ((_ ||| _) ||| (_ ||| _))
    rw [Nat.lor_assoc]
    rfl
  · have h0 : bit v k ||| bit v (Nat.add k 78) = 0 := Nat.eq_of_beq_eq_true h
    have h1 : bit v k = 0 := (Nat.or_eq_zero_iff.1 h0).1
    have h2 : bit v (Nat.add k 78) = 0 := (Nat.or_eq_zero_iff.1 h0).2
    unfold blk4
    rw [h1, h2]
    change acc = acc ||| ((0 <<< _ ||| 0 <<< _) ||| (0 <<< _ ||| (0 ^^^ 0) <<< _))
    simp

@[expose] noncomputable def orRec (E : ℕ → ℕ) (acc n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) acc (fun k acc => Nat.lor acc (E k)) n

theorem testBit_orRec (E : ℕ → ℕ) (acc n p : ℕ) :
    (orRec E acc n).testBit p = true ↔ acc.testBit p = true ∨ ∃ k < n, (E k).testBit p = true := by
  induction n with
  | zero => simp [orRec]
  | succ n ih =>
    change ((orRec E acc n) ||| E n).testBit p = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro ((h | ⟨k, hk, h⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, h⟩
      · exact Or.inr ⟨n, by omega, h⟩
    · rintro (h | ⟨k, hk, h⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hkn : k = n
        · subst hkn
          exact Or.inr h
        · exact Or.inl (Or.inr ⟨k, by omega, h⟩)

theorem blowCol_eq (l v acc : ℕ) : blowCol l v acc = orRec (blk4 l v) acc 78 := by
  unfold blowCol orRec
  exact congrArg (fun f => Nat.rec (motive := fun _ => ℕ) acc f 78)
    (funext fun k => funext fun acc => blowCol_step l v k acc)

@[expose] noncomputable def rootRec (col : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun l acc => orRec (blk4 l (col l)) acc 78) n

theorem rootB_eq (codes bits r c₀ c₁ : ℕ) :
    rootB codes bits r c₀ c₁ = rootRec (rootColK codes bits r c₀ c₁) 78 := by
  have h : (fun l acc => letN acc fun acc => blowCol l (rootColK codes bits r c₀ c₁ l) acc) =
      (fun l acc => orRec (blk4 l (rootColK codes bits r c₀ c₁ l)) acc 78) :=
    funext fun l => funext fun acc => (letN_eq _ _).trans (blowCol_eq _ _ _)
  unfold rootB rootRec
  rw [h]
  rfl

theorem testBit_rootRec (col : ℕ → ℕ) (n p : ℕ) :
    (rootRec col n).testBit p = true ↔ ∃ l < n, ∃ k < 78, (blk4 l (col l) k).testBit p = true := by
  induction n with
  | zero => simp [rootRec]
  | succ n ih =>
    change (orRec (blk4 n (col n)) (rootRec col n) 78).testBit p = true ↔ _
    rw [testBit_orRec, ih]
    constructor
    · rintro (⟨l, hl, h⟩ | h)
      · exact ⟨l, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨l, hl, h⟩
      by_cases hln : l = n
      · subst hln
        exact Or.inr h
      · exact Or.inl ⟨l, by omega, h⟩

theorem testBit_blk4 (l v k p : ℕ) : (blk4 l v k).testBit p = true ↔
    (p = 312 * k + 2 * l ∧ v.testBit k = true) ∨
    (p = 312 * k + 2 * l + 1 ∧ v.testBit (k + 78) = true) ∨
    (p = 312 * k + 156 + 2 * l ∧ v.testBit (k + 78) = true) ∨
    (p = 312 * k + 156 + 2 * l + 1 ∧ xor (v.testBit k) (v.testBit (k + 78)) = true) := by
  unfold blk4
  rw [bit_eq, bit_eq, toNat_xor]
  change (((_ ||| _) ||| (_ ||| _) : ℕ)).testBit p = true ↔ _
  simp only [Nat.testBit_or, testBit_toNat_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  have e1 : Nat.add (Nat.mul 312 k) (Nat.mul 2 l) = 312 * k + 2 * l := rfl
  have e2 : Nat.add (Nat.mul 312 k) (Nat.add (Nat.mul 2 l) 1) = 312 * k + 2 * l + 1 := by
    change 312 * k + (2 * l + 1) = _
    omega
  have e3 : Nat.add (Nat.add (Nat.mul 312 k) 156) (Nat.mul 2 l) = 312 * k + 156 + 2 * l := rfl
  have e4 : Nat.add (Nat.add (Nat.mul 312 k) 156) (Nat.add (Nat.mul 2 l) 1) =
      312 * k + 156 + 2 * l + 1 := by
    change 312 * k + 156 + (2 * l + 1) = _
    omega
  have e5 : Nat.add k 78 = k + 78 := rfl
  rw [e1, e2, e3, e4, e5]
  tauto

theorem rootRec_lt (col : ℕ → ℕ) : rootRec col 78 < 2 ^ 24336 := by
  apply Nat.lt_pow_two_of_testBit
  intro p hp
  cases h : (rootRec col 78).testBit p
  · rfl
  · obtain ⟨l, hl, k, hk, h'⟩ := (testBit_rootRec col 78 p).1 h
    rw [testBit_blk4] at h'
    omega

theorem rep_rootB (codes bits r : ℕ) (b₀ b₁ : Bool) (hr : r < 78)
    (hc : ∀ l < 78, code codes r l < 136) :
    Rep (rootB codes bits r b₀.toNat b₁.toNat) (toMat (Native.rootMat codes bits r b₀ b₁)) := by
  rw [rootB_eq]
  refine rep_of_testBit (rootRec_lt _) fun k l a b => ?_
  have hcol : (Native.rootMat codes bits r b₀ b₁).getD l (0, 0) =
      Native.rootCol codes bits r b₀ b₁ l := by
    simp [Native.rootMat, Array.getD_eq_getD_getElem?, l.2]
  rw [hcol]
  obtain ⟨h0, h1⟩ := testBit_rootColK codes bits r l b₀ b₁ hr l.2 (hc l l.2) k k.2
  rw [← h0, ← h1, Bool.eq_iff_iff, testBit_rootRec]
  have hk := k.2
  have hl := l.2
  set v := rootColK codes bits r b₀.toNat b₁.toNat
  fin_cases a <;> fin_cases b <;> simp only [bb] <;> constructor
  all_goals first
    | (rintro ⟨l', hl', k', hk', h⟩
       rw [testBit_blk4] at h
       rcases h with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ <;>
         simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at e <;>
         first
         | (have : l' = l := by omega
            have : k' = k := by omega
            subst_vars
            simpa using h)
         | omega)
    | (intro h
       refine ⟨l, hl, k, hk, ?_⟩
       rw [testBit_blk4]
       simp_all)

end CFSG.KC.Misc.E6Std

end
