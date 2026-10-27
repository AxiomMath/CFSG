module

public import Certificates.Data.Kernel.Misc.E6Std
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.Misc.E6Std

open CFSG.KC.Misc

attribute [local irreducible] rowStarts fullRow oneB

set_option exponentiation.threshold 25000

@[expose] def toZ (b : Bool) : ZMod 2 := if b then 1 else 0

theorem toZ_xor (a b : Bool) : toZ (xor a b) = toZ a + toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_and (a b : Bool) : toZ (a && b) = toZ a * toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_injective : Function.Injective toZ := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

@[expose] def decB (N : ℕ) : Matrix (Fin 156) (Fin 156) (ZMod 2) :=
  Matrix.of fun i j => toZ (N.testBit (156 * i + j))

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by
  cases y <;> rfl

theorem testBit_one (r : ℕ) : (1 : ℕ).testBit r = decide (r = 0) := by
  rcases r with _ | r
  · rfl
  · rw [Nat.testBit_succ]
    simp

@[expose] def stride (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 2 ^ s * stride s n

theorem stride_zero (s : ℕ) : stride s 0 = 0 := rfl

theorem stride_succ (s n : ℕ) : stride s (n + 1) = 1 + 2 ^ s * stride s n := rfl

attribute [irreducible] stride

theorem testBit_mul_stride {s T : ℕ} (hT : T < 2 ^ s) (n i : ℕ) {j : ℕ} (hj : j < s) :
    (T * stride s n).testBit (s * i + j) = (decide (i < n) && T.testBit j) := by
  induction n generalizing i with
  | zero => simp [stride_zero]
  | succ n ih =>
    have e : T * stride s (n + 1) = 2 ^ s * (T * stride s n) + T := by
      rw [stride_succ]
      ring
    rw [e, Nat.testBit_two_pow_mul_add _ hT]
    rcases i with _ | i
    · simp [hj]
    · have h1 : ¬ s * (i + 1) + j < s := by nlinarith
      have h2 : s * (i + 1) + j - s = s * i + j := by
        rw [Nat.mul_succ]
        omega
      simp only [h1, ↓reduceIte, h2, ih]
      simp

theorem stride_mul (s n : ℕ) : stride s n * (2 ^ s - 1) = 2 ^ (s * n) - 1 := by
  induction n with
  | zero => simp [stride_zero]
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (s * n) := Nat.one_le_two_pow
    have h3 : 2 ^ (s * (n + 1)) = 2 ^ s * 2 ^ (s * n) := by
      rw [Nat.mul_succ, pow_add, mul_comm]
    have h4 : 1 ≤ 2 ^ s * 2 ^ (s * n) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [stride_succ, h3]
    zify [h1, h2, h4] at ih ⊢
    have ih' : (stride s n : ℤ) * (2 ^ s - 1) = 2 ^ (s * n) - 1 := by exact_mod_cast ih
    linear_combination (2 : ℤ) ^ s * ih'

theorem two_le_two_pow {s : ℕ} (hs : 0 < s) : 2 ≤ 2 ^ s :=
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs

theorem div_stride (s n : ℕ) (hs : 0 < s) :
    (2 ^ (s * n) - 1) / (2 ^ s - 1) = stride s n := by
  have h1 : 0 < 2 ^ s - 1 := by
    have := two_le_two_pow hs
    omega
  rw [← stride_mul s n, Nat.mul_div_cancel _ h1]

theorem shl_one (n : ℕ) : Nat.shiftLeft 1 n = 2 ^ n := Nat.one_shiftLeft n

theorem div_sub_form (a b : ℕ) : Nat.div (Nat.sub a 1) (Nat.sub b 1) = (a - 1) / (b - 1) := rfl

theorem rowStarts_eq : rowStarts = stride 156 156 := by
  have h := div_stride 156 156 (by norm_num)
  simp only [Nat.reduceMul] at h
  have e : rowStarts = (2 ^ 24336 - 1) / (2 ^ 156 - 1) := by
    unfold rowStarts
    rw [div_sub_form, shl_one, shl_one]
  exact e.trans h

theorem fullRow_eq : fullRow = 2 ^ 156 - 1 := by
  unfold fullRow
  rw [shl_one]
  rfl

theorem oneB_eq : oneB = stride 157 156 := by
  have h := div_stride 157 156 (by norm_num)
  simp only [Nat.reduceMul] at h
  have e : oneB = (2 ^ 24492 - 1) / (2 ^ 157 - 1) := by
    unfold oneB
    rw [div_sub_form, shl_one, shl_one]
  exact e.trans h

theorem mod_of_starts {s x : ℕ} (hs : 0 < s) (hx : ∀ p, x.testBit p = true → p % s = 0) :
    x % 2 ^ s = if x.testBit 0 then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_mod_two_pow]
  rcases p with _ | p
  · cases x.testBit 0 <;> simp [hs]
  · have h1 : (1 : ℕ).testBit (p + 1) = false := by
      rw [testBit_one]
      simp
    by_cases hp : p + 1 < s
    · have : x.testBit (p + 1) = false := by
        cases h : x.testBit (p + 1)
        · rfl
        · have := hx _ h
          rw [Nat.mod_eq_of_lt hp] at this
          omega
      cases h0 : x.testBit 0 <;> simp [hp, this, h1]
    · cases h0 : x.testBit 0 <;> simp [hp, h1]

theorem spread_split (s x : ℕ) : x * (2 ^ s - 1) = 2 ^ s * ((x >>> s) * (2 ^ s - 1)) +
    (x % 2 ^ s) * (2 ^ s - 1) := by
  rw [Nat.shiftRight_eq_div_pow]
  conv_lhs => rw [← Nat.div_add_mod x (2 ^ s)]
  ring

theorem mod_mul_lt {s x : ℕ} (hs : 0 < s) (hx : ∀ p, x.testBit p = true → p % s = 0) :
    (x % 2 ^ s) * (2 ^ s - 1) < 2 ^ s := by
  rw [mod_of_starts hs hx]
  split_ifs
  · rw [one_mul]
    exact Nat.sub_lt Nat.one_le_two_pow one_pos
  · rw [zero_mul]
    exact Nat.two_pow_pos _

theorem testBit_spread {s x : ℕ} (hx : ∀ p, x.testBit p = true → p % s = 0) (i : ℕ) {j : ℕ}
    (hj : j < s) : (x * (2 ^ s - 1)).testBit (s * i + j) = x.testBit (s * i) := by
  have hs : 0 < s := by omega
  induction i generalizing x with
  | zero =>
    rw [spread_split, Nat.testBit_two_pow_mul_add _ (mod_mul_lt hs hx), Nat.mul_zero,
      Nat.zero_add]
    simp only [hj, ↓reduceIte]
    rw [mod_of_starts hs hx]
    cases x.testBit 0
    · simp
    · simp only [↓reduceIte, one_mul, Nat.testBit_two_pow_sub_one, decide_eq_true hj]
  | succ i ih =>
    have hx' : ∀ p, (x >>> s).testBit p = true → p % s = 0 := by
      intro p hp
      rw [Nat.testBit_shiftRight] at hp
      have := hx _ hp
      rw [Nat.add_mod_left] at this
      exact this
    have e1 : s * (i + 1) + j = s + (s * i + j) := by ring
    have e2 : s * (i + 1) = s + s * i := by ring
    have h1 : ¬ s + (s * i + j) < s := by omega
    rw [spread_split, Nat.testBit_two_pow_mul_add _ (mod_mul_lt hs hx), e1, e2]
    simp only [h1, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [ih hx', Nat.testBit_shiftRight]

theorem testBit_rowStarts (p : ℕ) :
    rowStarts.testBit p = (decide (p / 156 < 156) && decide (p % 156 = 0)) := by
  have e : p = 156 * (p / 156) + p % 156 := (Nat.div_add_mod p 156).symm
  have h := testBit_mul_stride (T := 1) (s := 156) (Nat.one_lt_two_pow (by decide)) 156 (p / 156)
    (Nat.mod_lt p (by decide : 0 < 156))
  rw [← e, one_mul, testBit_one] at h
  rw [rowStarts_eq, h]

@[expose] noncomputable def term (A B k : ℕ) : ℕ :=
  (((A >>> k) &&& rowStarts) * fullRow) &&& (((B >>> (156 * k)) &&& fullRow) * rowStarts)

theorem testBit_term (A B k : ℕ) {i j : ℕ} (hi : i < 156) (hj : j < 156) :
    (term A B k).testBit (156 * i + j) = (A.testBit (156 * i + k) && B.testBit (156 * k + j)) := by
  have hX : ∀ p, ((A >>> k) &&& rowStarts).testBit p = true → p % 156 = 0 := by
    intro p hp
    rw [Nat.testBit_and, testBit_rowStarts] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.2.2
  have hY : (B >>> (156 * k)) &&& (2 ^ 156 - 1) < 2 ^ 156 :=
    Nat.and_lt_two_pow _ (Nat.sub_lt Nat.one_le_two_pow one_pos)
  have h1 : (((A >>> k) &&& rowStarts) * fullRow).testBit (156 * i + j) = A.testBit (156 * i + k) := by
    rw [fullRow_eq, testBit_spread hX i hj, Nat.testBit_and, testBit_rowStarts,
      Nat.testBit_shiftRight, Nat.mul_div_cancel_left _ (by norm_num : 0 < 156), Nat.mul_mod_right,
      decide_eq_true hi, Nat.add_comm k]
    simp
  have h2 : (((B >>> (156 * k)) &&& fullRow) * rowStarts).testBit (156 * i + j) =
      B.testBit (156 * k + j) := by
    rw [fullRow_eq, rowStarts_eq, testBit_mul_stride hY 156 i hj, Nat.testBit_and,
      Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight, decide_eq_true hi, decide_eq_true hj]
    simp
  rw [term, Nat.testBit_and, h1, h2]

theorem term_lt (A B k : ℕ) : term A B k < 2 ^ 24336 := by
  have hY : (B >>> (156 * k)) &&& (2 ^ 156 - 1) ≤ 2 ^ 156 - 1 := Nat.and_le_right
  have hm : ∀ m : ℕ, 2 ^ m - 1 < 2 ^ m := fun m => Nat.sub_lt (Nat.two_pow_pos m) Nat.one_pos
  have h0 : 2 ^ (156 * 156) - 1 < 2 ^ 24336 := by
    simp only [Nat.reduceMul]
    exact hm 24336
  have h3 : ((B >>> (156 * k)) &&& (2 ^ 156 - 1)) * stride 156 156 < 2 ^ 24336 := by
    calc _ ≤ (2 ^ 156 - 1) * stride 156 156 := Nat.mul_le_mul_right _ hY
      _ = 2 ^ (156 * 156) - 1 := by rw [mul_comm, stride_mul]
      _ < 2 ^ 24336 := h0
  rw [term, fullRow_eq, rowStarts_eq]
  exact lt_of_le_of_lt Nat.and_le_right h3

@[expose] noncomputable def mulPart (A B n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc ^^^ term A B k) n

theorem mulPart_eq (A B : ℕ) (n : ℕ) : mulPart A B n =
    Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun k acc => Nat.xor acc (Nat.land
      (Nat.mul (Nat.land (Nat.shiftRight A k) rowStarts) fullRow)
      (Nat.mul (Nat.land (Nat.shiftRight B (Nat.mul (nat_lit 156) k)) fullRow) rowStarts))) n :=
  rfl

theorem mulB_eq (A B : ℕ) : mulB A B = mulPart A B 156 := by
  unfold mulB
  exact (letN_eq _ _).trans ((letN_eq _ _).trans ((letN_eq _ _).trans ((letN_eq _ _).trans
    (mulPart_eq A B 156).symm)))

theorem mulPart_lt (A B n : ℕ) : mulPart A B n < 2 ^ 24336 := by
  induction n with
  | zero => exact Nat.two_pow_pos _
  | succ n ih => exact Nat.xor_lt_two_pow ih (term_lt A B n)

theorem toZ_mulPart (A B n : ℕ) {i j : ℕ} (hi : i < 156) (hj : j < 156) :
    toZ ((mulPart A B n).testBit (156 * i + j)) =
      ∑ k ∈ Finset.range n, toZ (A.testBit (156 * i + k)) * toZ (B.testBit (156 * k + j)) := by
  induction n with
  | zero => simp [mulPart, toZ]
  | succ n ih =>
    change toZ ((mulPart A B n ^^^ term A B n).testBit _) = _
    rw [Nat.testBit_xor, toZ_xor, ih, Finset.sum_range_succ, testBit_term A B n hi hj, toZ_and]

attribute [irreducible] mulPart

theorem decB_mulB (A B : ℕ) : decB (mulB A B) = decB A * decB B := by
  ext i j
  have h := toZ_mulPart A B 156 i.2 j.2
  rw [Finset.sum_range, ← mulB_eq] at h
  simp only [decB, Matrix.of_apply, Matrix.mul_apply]
  exact h

theorem mulB_lt (A B : ℕ) : mulB A B < 2 ^ 24336 := by
  rw [mulB_eq]
  exact mulPart_lt A B 156

theorem testBit_oneB {i j : ℕ} (hi : i < 156) (hj : j < 156) :
    oneB.testBit (156 * i + j) = decide (i = j) := by
  have e : 156 * i + j = 157 * ((156 * i + j) / 157) + (156 * i + j) % 157 :=
    (Nat.div_add_mod _ 157).symm
  have h := testBit_mul_stride (T := 1) (s := 157) (by norm_num) 156 ((156 * i + j) / 157)
    (Nat.mod_lt (156 * i + j) (by norm_num : 0 < 157))
  rw [← e, one_mul, testBit_one] at h
  rw [oneB_eq, h]
  by_cases hij : i = j
  · subst hij
    have h1 : (156 * i + i) / 157 = i := by omega
    have h2 : (156 * i + i) % 157 = 0 := by omega
    simp [h1, h2, hi]
  · have h2 : (156 * i + j) % 157 ≠ 0 := by omega
    simp [h2, hij]

theorem oneB_lt : oneB < 2 ^ 24336 := by
  rw [oneB_eq]
  apply Nat.lt_pow_two_of_testBit
  intro p hp
  have e : p = 157 * (p / 157) + p % 157 := (Nat.div_add_mod p 157).symm
  have h := testBit_mul_stride (T := 1) (s := 157) (by norm_num) 156 (p / 157)
    (Nat.mod_lt p (by norm_num : 0 < 157))
  rw [← e, one_mul, testBit_one] at h
  rw [h]
  by_cases h0 : p % 157 = 0
  · have : ¬ p / 157 < 156 := by omega
    simp [this]
  · simp [h0]

theorem decB_oneB : decB oneB = 1 := by
  ext i j
  simp only [decB, Matrix.of_apply, Matrix.one_apply]
  rw [testBit_oneB i.2 j.2]
  by_cases h : i = j
  · subst h
    simp [toZ]
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, h', toZ]

theorem eq_of_decB_eq {N N' : ℕ} (hN : N < 2 ^ 24336) (hN' : N' < 2 ^ 24336)
    (h : decB N = decB N') : N = N' := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 24336
  · have e : p = 156 * (p / 156) + p % 156 := (Nat.div_add_mod p 156).symm
    have h1 := congrFun (congrFun h ⟨p / 156, by omega⟩) ⟨p % 156, Nat.mod_lt _ (by norm_num)⟩
    simp only [decB, Matrix.of_apply] at h1
    rw [e]
    exact toZ_injective h1
  · have hle : 2 ^ 24336 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hN hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hN' hle)]

theorem decB_powB (P n : ℕ) : decB (powB P n) = decB P ^ n := by
  induction n with
  | zero => exact decB_oneB
  | succ n ih =>
    change decB (mulB (powB P n) P) = _
    rw [decB_mulB, ih, pow_succ]

theorem powB_lt (P n : ℕ) : powB P n < 2 ^ 24336 := by
  cases n with
  | zero => exact oneB_lt
  | succ n => exact mulB_lt _ _

end CFSG.KC.Misc.E6Std

end
