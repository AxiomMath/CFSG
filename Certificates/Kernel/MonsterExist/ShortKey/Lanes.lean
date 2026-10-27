module

public import Certificates.Kernel.MonsterExist.ShortKey.Defs
public import Aesop.BuiltinRules
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Std.Tactic.BVDecide.Normalize.BitVec
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CertificateChecks.MonsterExist.ShortKey

@[expose] def lsum (W : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ (W * n) * f n + lsum W f n

variable {W : ℕ}

theorem maskW_eq (w : ℕ) : maskW w = 2 ^ w - 1 := by
  change (1 <<< w) - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem land_maskW (x w : ℕ) : Nat.land x (maskW w) = x % 2 ^ w := by
  rw [maskW_eq]
  exact Nat.and_two_pow_sub_one_eq_mod x w

theorem laneW_eq (v k : ℕ) : laneW W v k = v / 2 ^ (W * k) % 2 ^ W := by
  unfold laneW
  rw [land_maskW]
  change (v >>> (W * k)) % 2 ^ W = _
  rw [Nat.shiftRight_eq_div_pow]

theorem lsum_lt {f : ℕ → ℕ} : ∀ {n}, (∀ k < n, f k < 2 ^ W) → lsum W f n < 2 ^ (W * n)
  | 0, _ => by simp [lsum]
  | n + 1, hf => by
    have ih := lsum_lt (n := n) fun k hk => hf k (Nat.lt_succ_of_lt hk)
    have h1 := hf n (Nat.lt_succ_self n)
    have e : 2 ^ (W * (n + 1)) = 2 ^ (W * n) * 2 ^ W := by rw [Nat.mul_succ, Nat.pow_add]
    rw [lsum, e]
    calc 2 ^ (W * n) * f n + lsum W f n < 2 ^ (W * n) * f n + 2 ^ (W * n) := by omega
      _ = 2 ^ (W * n) * (f n + 1) := by ring
      _ ≤ 2 ^ (W * n) * 2 ^ W := Nat.mul_le_mul_left _ h1

theorem testBit_lsum (hW : 0 < W) {f : ℕ → ℕ} : ∀ {n}, (∀ k < n, f k < 2 ^ W) → ∀ j,
    (lsum W f n).testBit j = if j < W * n then (f (j / W)).testBit (j % W) else false
  | 0, _, j => by simp [lsum]
  | n + 1, hf, j => by
    have hf' : ∀ k < n, f k < 2 ^ W := fun k hk => hf k (Nat.lt_succ_of_lt hk)
    rw [lsum, Nat.testBit_two_pow_mul_add _ (lsum_lt hf'), testBit_lsum hW hf' j]
    by_cases h1 : j < W * n
    · have h2 : j < W * (n + 1) := by rw [Nat.mul_succ]; omega
      simp [h1, h2]
    · simp only [h1, ↓reduceIte]
      have hq : W * n ≤ j := Nat.le_of_not_lt h1
      by_cases h2 : j < W * (n + 1)
      · have hjn : j / W = n := by
          have h2' : j < W * n + W := by rw [Nat.mul_succ] at h2; exact h2
          have hc := Nat.mul_comm W n
          exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega)
        have hjm : j % W = j - W * n := by
          have := Nat.mod_add_div j W
          rw [hjn] at this
          omega
        simp only [h2, ↓reduceIte, hjn, hjm]
      · simp only [h2, ↓reduceIte]
        apply Nat.testBit_lt_two_pow
        have h3 : W ≤ j - W * n := by rw [Nat.mul_succ] at h2; omega
        exact lt_of_lt_of_le (hf n (Nat.lt_succ_self n)) (Nat.pow_le_pow_right (by norm_num) h3)

theorem lsum_ext (hW : 0 < W) {f g : ℕ → ℕ} {n : ℕ} (hf : ∀ k < n, f k < 2 ^ W)
    (hg : ∀ k < n, g k < 2 ^ W) : lsum W f n = lsum W g n ↔ ∀ k < n, f k = g k := by
  constructor
  · intro h k hk
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < W
    · have := congrArg (fun x => x.testBit (W * k + i)) h
      simp only [testBit_lsum hW hf, testBit_lsum hW hg] at this
      have h1 : W * k + i < W * n := by
        have : W * (k + 1) ≤ W * n := Nat.mul_le_mul_left _ hk
        rw [Nat.mul_succ] at this
        omega
      have h2 : (W * k + i) / W = k := by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hi, Nat.zero_add]
      have h3 : (W * k + i) % W = i := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
      simpa [h1, h2, h3] using this
    · have hi' : W ≤ i := Nat.le_of_not_lt hi
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf k hk) (Nat.pow_le_pow_right (by norm_num) hi')),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (hg k hk) (Nat.pow_le_pow_right (by norm_num) hi'))]
  · intro h
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [lsum, lsum, h n (Nat.lt_succ_self n),
        ih (fun k hk => hf k (Nat.lt_succ_of_lt hk)) (fun k hk => hg k (Nat.lt_succ_of_lt hk))
          (fun k hk => h k (Nat.lt_succ_of_lt hk))]

theorem testBit_laneW (v k i : ℕ) (hi : i < W) :
    (laneW W v k).testBit i = v.testBit (W * k + i) := by
  rw [laneW_eq, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and, Nat.testBit_div_two_pow,
    Nat.add_comm]

theorem laneW_lt (v k : ℕ) : laneW W v k < 2 ^ W := by
  rw [laneW_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos W)

theorem eq_lsum_laneW (hW : 0 < W) {v n : ℕ} (hv : v < 2 ^ (W * n)) :
    v = lsum W (laneW W v) n := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_lsum hW (fun k _ => laneW_lt v k)]
  split_ifs with h
  · rw [testBit_laneW v _ _ (Nat.mod_lt j hW), Nat.div_add_mod]
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_of_not_lt h)))

theorem laneW_lsum (hW : 0 < W) {f : ℕ → ℕ} {n : ℕ} (hf : ∀ k < n, f k < 2 ^ W) {k : ℕ}
    (hk : k < n) : laneW W (lsum W f n) k = f k := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < W
  · rw [testBit_laneW _ _ _ hi, testBit_lsum hW hf]
    have h1 : W * k + i < W * n := by
      have : W * (k + 1) ≤ W * n := Nat.mul_le_mul_left _ hk
      rw [Nat.mul_succ] at this
      omega
    have h2 : (W * k + i) / W = k := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hi, Nat.zero_add]
    have h3 : (W * k + i) % W = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
    simp [h1, h2, h3]
  · have hi' : W ≤ i := Nat.le_of_not_lt hi
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (laneW_lt _ k) (Nat.pow_le_pow_right (by norm_num) hi')),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf k hk) (Nat.pow_le_pow_right (by norm_num) hi'))]

theorem xor_lsum (hW : 0 < W) {f g : ℕ → ℕ} {n : ℕ} (hf : ∀ k < n, f k < 2 ^ W)
    (hg : ∀ k < n, g k < 2 ^ W) : lsum W f n ^^^ lsum W g n = lsum W (fun k => f k ^^^ g k) n := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_lsum hW hf, testBit_lsum hW hg,
    testBit_lsum hW (fun k hk => Nat.xor_lt_two_pow (hf k hk) (hg k hk))]
  split_ifs with h
  · have hk : j / W < n := by
      rw [Nat.div_lt_iff_lt_mul hW, Nat.mul_comm]
      exact h
    rw [Nat.testBit_xor]
  · rfl

theorem lor_lsum (hW : 0 < W) {f g : ℕ → ℕ} {n : ℕ} (hf : ∀ k < n, f k < 2 ^ W)
    (hg : ∀ k < n, g k < 2 ^ W) : lsum W f n ||| lsum W g n = lsum W (fun k => f k ||| g k) n := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, testBit_lsum hW hf, testBit_lsum hW hg,
    testBit_lsum hW (fun k hk => Nat.or_lt_two_pow (hf k hk) (hg k hk))]
  split_ifs with h
  · rw [Nat.testBit_or]
  · rfl

theorem land_lsum (hW : 0 < W) {f g : ℕ → ℕ} {n : ℕ} (hf : ∀ k < n, f k < 2 ^ W)
    (hg : ∀ k < n, g k < 2 ^ W) : lsum W f n &&& lsum W g n = lsum W (fun k => f k &&& g k) n := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, testBit_lsum hW hf, testBit_lsum hW hg,
    testBit_lsum hW (fun k hk => lt_of_le_of_lt Nat.and_le_left (hf k hk))]
  split_ifs with h
  · rw [Nat.testBit_and]
  · rfl

theorem mul_lsum (c : ℕ) (f : ℕ → ℕ) : ∀ n, c * lsum W f n = lsum W (fun k => c * f k) n
  | 0 => by simp [lsum]
  | n + 1 => by rw [lsum, lsum, ← mul_lsum c f n]; ring

theorem lsum_mono {f g : ℕ → ℕ} : ∀ {n}, (∀ k < n, f k ≤ g k) → lsum W f n ≤ lsum W g n
  | 0, _ => le_rfl
  | n + 1, h => by
    rw [lsum, lsum]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (h n (Nat.lt_succ_self n)))
      (lsum_mono fun k hk => h k (Nat.lt_succ_of_lt hk))

theorem lsum_sub_ones {f : ℕ → ℕ} : ∀ {n}, (∀ k < n, 1 ≤ f k) →
    lsum W f n - lsum W (fun _ => 1) n = lsum W (fun k => f k - 1) n
  | 0, _ => rfl
  | n + 1, h => by
    have ih := lsum_sub_ones (n := n) fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hm := lsum_mono (W := W) (f := fun _ => 1) (g := f) (n := n)
      fun k hk => h k (Nat.lt_succ_of_lt hk)
    have h1 := h n (Nat.lt_succ_self n)
    rw [lsum, lsum, lsum, ← ih]
    have e : 2 ^ (W * n) * f n = 2 ^ (W * n) * (f n - 1) + 2 ^ (W * n) := by
      rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ h1)]
    rw [e, Nat.mul_one]
    omega

theorem lsum_ones (hW : 0 < W) : ∀ n, (2 ^ W - 1) * lsum W (fun _ => 1) n = 2 ^ (W * n) - 1
  | 0 => by simp [lsum]
  | n + 1 => by
    rw [lsum, Nat.mul_add, lsum_ones hW n, Nat.mul_one, Nat.mul_succ, Nat.pow_add]
    have h1 : 1 ≤ 2 ^ (W * n) := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    have e : (2 ^ W - 1) * 2 ^ (W * n) = 2 ^ (W * n) * 2 ^ W - 2 ^ (W * n) := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
    rw [e]
    have h3 : 2 ^ (W * n) ≤ 2 ^ (W * n) * 2 ^ W := Nat.le_mul_of_pos_right _ (by omega)
    omega

theorem onesL_eq (hW : 0 < W) (n : ℕ) : onesL W n = lsum W (fun _ => 1) n := by
  unfold onesL
  rw [maskW_eq, maskW_eq]
  change (2 ^ (W * n) - 1) / (2 ^ W - 1) = _
  rw [← lsum_ones hW n]
  have : 0 < 2 ^ W - 1 := by
    have : 2 ≤ 2 ^ W := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
    omega
  exact Nat.mul_div_cancel_left _ this

theorem testBit_top {c : ℕ} (hW : 0 < W) (hc : c < 2 ^ W) :
    c.testBit (W - 1) = true ↔ 2 ^ (W - 1) ≤ c := by
  have e : 2 ^ W = 2 * 2 ^ (W - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  have hlt : c / 2 ^ (W - 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    omega
  rw [Nat.mod_eq_of_lt hlt]
  constructor
  · intro h
    have := Nat.div_mul_le_self c (2 ^ (W - 1))
    rw [h, Nat.one_mul] at this
    exact this
  · intro h
    have h1 : 1 ≤ c / 2 ^ (W - 1) := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 (by omega)
    omega

theorem and_top {c : ℕ} : c &&& 2 ^ (W - 1) = 2 ^ (W - 1) ↔ c.testBit (W - 1) = true := by
  constructor
  · intro h
    have := congrArg (fun x => x.testBit (W - 1)) h
    simp only [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hi : W - 1 = i
    · subst hi
      simp [h]
    · simp [hi]

theorem xor_eq_zero_iff' {a b : ℕ} : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· ^^^ b) h
    simpa [Nat.xor_assoc] using this
  · rintro rfl
    exact Nat.xor_self a

theorem absentL_iff {n v d : ℕ} (hW : 0 < W) (hv : v < 2 ^ (W * n))
    (hl : ∀ k < n, laneW W v k < 2 ^ (W - 1)) (hd : d < 2 ^ (W - 1)) :
    absentL W n v d = true ↔ ∀ k < n, laneW W v k ≠ d := by
  have e2 : 2 ^ W = 2 * 2 ^ (W - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hhalf : ∀ x < 2 ^ (W - 1), x < 2 ^ W := fun x hx => by omega
  set y : ℕ → ℕ := fun k => laneW W v k ^^^ d with hy
  have hyl : ∀ k < n, y k < 2 ^ (W - 1) := fun k hk => Nat.xor_lt_two_pow (hl k hk) hd
  have hv' := eq_lsum_laneW hW hv
  have ho := onesL_eq hW n
  have hdo : d * onesL W n = lsum W (fun _ => d) n := by
    rw [ho, mul_lsum]
    simp
  have hh : Nat.shiftLeft (onesL W n) (W - 1) = lsum W (fun _ => 2 ^ (W - 1)) n := by
    change onesL W n <<< (W - 1) = _
    rw [Nat.shiftLeft_eq, ho, Nat.mul_comm, mul_lsum]
    simp
  have hx : v ^^^ d * onesL W n = lsum W y n := by
    rw [hdo]
    conv_lhs => rw [hv']
    rw [xor_lsum hW (fun k _ => laneW_lt v k) (fun _ _ => hhalf d hd)]
  have hor : lsum W (fun _ => 2 ^ (W - 1)) n ||| lsum W y n =
      lsum W (fun k => y k + 2 ^ (W - 1)) n := by
    rw [lor_lsum hW (fun _ _ => by omega) (fun k hk => hhalf _ (hyl k hk))]
    rw [lsum_ext hW (fun k hk => Nat.or_lt_two_pow (by omega) (hhalf _ (hyl k hk)))
      (fun k hk => by have := hyl k hk; omega)]
    intro k hk
    rw [Nat.or_comm]
    exact Nat.or_two_pow_eq_add_of_lt (hyl k hk)
  have hsub : lsum W (fun k => y k + 2 ^ (W - 1)) n - lsum W (fun _ => 1) n =
      lsum W (fun k => y k + 2 ^ (W - 1) - 1) n :=
    lsum_sub_ones fun k _ => by have := Nat.one_le_two_pow (n := W - 1); omega
  have hc : ∀ k < n, y k + 2 ^ (W - 1) - 1 < 2 ^ W := fun k hk => by have := hyl k hk; omega
  have hand : lsum W (fun k => y k + 2 ^ (W - 1) - 1) n &&& lsum W (fun _ => 2 ^ (W - 1)) n =
      lsum W (fun k => (y k + 2 ^ (W - 1) - 1) &&& 2 ^ (W - 1)) n :=
    land_lsum hW hc (fun _ _ => by omega)
  unfold absentL
  change Nat.beq ((((Nat.shiftLeft (onesL W n) (W - 1)) ||| (v ^^^ d * onesL W n)) - onesL W n) &&&
    Nat.shiftLeft (onesL W n) (W - 1)) (Nat.shiftLeft (onesL W n) (W - 1)) = true ↔ _
  rw [hh, hx, hor, ho, hsub, hand, Nat.beq_eq,
    lsum_ext hW (fun k hk => lt_of_le_of_lt Nat.and_le_right (by omega)) (fun _ _ => by omega)]
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  rw [and_top, testBit_top hW (hc k hk)]
  have h1 : 2 ^ (W - 1) ≤ y k + 2 ^ (W - 1) - 1 ↔ y k ≠ 0 := by omega
  rw [h1, hy]
  exact not_congr xor_eq_zero_iff'

end CertificateChecks.MonsterExist.ShortKey

end
