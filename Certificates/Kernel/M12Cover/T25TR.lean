module

public import Certificates.Kernel.M12Cover.T25Bind
public import CFSG.Certificates.Kernel.Spor.PK.Basic
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelM12T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.M12Dec CFSG.KC.M12Trans
open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.M12Cover.InternalSylow

@[expose] noncomputable def t25Lanes (F R : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun m s => Nat.add s (Nat.shiftLeft (Nat.add
      (Nat.land (Nat.shiftRight F
        (Nat.land (Nat.shiftRight R (Nat.mul (nat_lit 12) m)) (nat_lit 63))) (nat_lit 1))
      (Nat.shiftLeft (Nat.land (Nat.shiftRight F
        (Nat.land (Nat.shiftRight R (Nat.add (Nat.mul (nat_lit 12) m) (nat_lit 6))) (nat_lit 63)))
        (nat_lit 1)) (nat_lit 12)))
      (Nat.mul (nat_lit 24) m))) (nat_lit 32)

@[expose] noncomputable def t25Sum (h : Nat) : Nat :=
  foldN 1485 (fun i s => Nat.add s
    (t25Lanes (Nat.land (Nat.shiftRight fTable (Nat.mul 64 (ppK i h))) (nat_lit 18446744073709551615))
      (rowsOf 6 PP (ihK i h)))) 0

@[expose] noncomputable def t25Row (h S : Nat) : Bool :=
  allN 64 fun k => Nat.beq (Nat.mod (Nat.add (Nat.add (Nat.add
    (Nat.land (Nat.shiftRight S (Nat.mul 12 k)) 4095) (muIdx h)) (muIdx k)) (muIdx (mIdx h k))) 2)
    (fIdx h k)

@[expose] noncomputable def fTRL (h : Nat) : Bool := strictB (t25Sum h) (t25Row h)

#lc_blocks T25TRL fTRL 64 1

theorem t25Row_neg : bIf(t25Row 5 (Nat.add (t25Sum 5) 1), false, true) = true := by quickRfl

noncomputable def t25Enc (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => t25Enc c n + c n * 4096 ^ n

theorem t25Enc_lt {c : ℕ → ℕ} : ∀ {n : ℕ}, (∀ k < n, c k < 4096) → t25Enc c n < 4096 ^ n
  | 0, _ => by simp [t25Enc]
  | n + 1, hc => by
    have h1 := t25Enc_lt (n := n) fun k hk => hc k (by omega)
    have h2 : c n * 4096 ^ n ≤ 4095 * 4096 ^ n :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (hc n (by omega)))
    rw [t25Enc, pow_succ]
    omega

theorem t25Enc_lane {c : ℕ → ℕ} : ∀ {n : ℕ}, (∀ k < n, c k < 4096) → ∀ k < n,
    t25Enc c n / 4096 ^ k % 4096 = c k
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, hc, k, hk => by
    rw [t25Enc]
    rcases Nat.lt_or_ge k n with hkn | hkn
    · have hp : c n * 4096 ^ n = (c n * 4096 ^ (n - k - 1)) * 4096 * 4096 ^ k := by
        rw [Nat.mul_assoc, Nat.mul_assoc, ← pow_succ', ← pow_add]
        congr 2
        omega
      rw [hp, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right]
      exact t25Enc_lane (fun j hj => hc j (by omega)) k hkn
    · have hkn' : k = n := by omega
      subst hkn'
      rw [Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt (t25Enc_lt fun j hj => hc j (by omega)), Nat.zero_add,
        Nat.mod_eq_of_lt (hc k (by omega))]

theorem t25Enc_zero : ∀ n, t25Enc (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by rw [t25Enc, t25Enc_zero n]; simp

theorem t25Enc_add (c d : ℕ → ℕ) : ∀ n, t25Enc (fun k => c k + d k) n = t25Enc c n + t25Enc d n
  | 0 => rfl
  | n + 1 => by
    rw [t25Enc, t25Enc, t25Enc, t25Enc_add c d n, Nat.add_mul]
    omega

theorem t25Enc_sum (t : ℕ → ℕ → ℕ) (m : ℕ) : ∀ n,
    ((List.range n).map fun i => t25Enc (t i) m).sum =
      t25Enc (fun k => ((List.range n).map fun i => t i k).sum) m
  | 0 => by simp [t25Enc_zero]
  | n + 1 => by
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [t25Enc_add, t25Enc_sum t m n]

theorem t25_foldr_add (t : ℕ → ℕ) : ∀ n s,
    (List.range n).foldr (fun i s => Nat.add s (t i)) s = s + ((List.range n).map t).sum
  | 0, s => by simp
  | n + 1, s => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, t25_foldr_add t n]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_eq]
    omega

theorem t25_sum_le (t : ℕ → ℕ) (ht : ∀ i, t i ≤ 1) : ∀ n, ((List.range n).map t).sum ≤ n
  | 0 => by simp
  | n + 1 => by
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    have := t25_sum_le t ht n
    have := ht n
    omega

noncomputable def t25G (F R x : ℕ) : ℕ := Nat.land (Nat.shiftRight F (Nat.land (Nat.shiftRight R x) 63)) 1

theorem t25G_le (F R x : ℕ) : t25G F R x ≤ 1 := by
  unfold t25G
  change _ &&& 1 ≤ 1
  rw [Nat.and_one_is_mod]
  omega

noncomputable def t25Step (F R : ℕ) : ℕ → ℕ → ℕ :=
  fun m s => Nat.add s (Nat.shiftLeft (Nat.add
      (Nat.land (Nat.shiftRight F
        (Nat.land (Nat.shiftRight R (Nat.mul (nat_lit 12) m)) (nat_lit 63))) (nat_lit 1))
      (Nat.shiftLeft (Nat.land (Nat.shiftRight F
        (Nat.land (Nat.shiftRight R (Nat.add (Nat.mul (nat_lit 12) m) (nat_lit 6))) (nat_lit 63)))
        (nat_lit 1)) (nat_lit 12)))
      (Nat.mul (nat_lit 24) m))

theorem t25Step_eq (F R m s : ℕ) : t25Step F R m s =
    s + (t25G F R (6 * (2 * m)) + t25G F R (6 * (2 * m + 1)) * 4096) * 4096 ^ (2 * m) := by
  unfold t25Step
  change s + ((t25G F R (12 * m) + t25G F R (12 * m + 6) <<< 12) <<< (24 * m)) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, show 6 * (2 * m) = 12 * m by ring,
    show 6 * (2 * m + 1) = 12 * m + 6 by ring,
    show (2 : ℕ) ^ (24 * m) = 4096 ^ (2 * m) by rw [pow_mul, pow_mul]; norm_num]

theorem t25_rec_enc (F R : ℕ) : ∀ n, Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (t25Step F R) n =
    t25Enc (fun k => t25G F R (6 * k)) (2 * n)
  | 0 => rfl
  | n + 1 => by
    have e : Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (t25Step F R) (n + 1) =
        t25Step F R n (Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (t25Step F R) n) := rfl
    rw [e, t25Step_eq, t25_rec_enc F R n, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, t25Enc,
      t25Enc, pow_succ]
    ring

theorem t25Lanes_eq (F R : ℕ) : t25Lanes F R = t25Enc (fun k => t25G F R (6 * k)) 64 :=
  t25_rec_enc F R 32

theorem t25_bit (a j k : ℕ) (hk : k < 64) :
    t25G (Nat.land (Nat.shiftRight fTable (Nat.mul 64 a)) (nat_lit 18446744073709551615))
      (rowsOf 6 PP j) (6 * k) = fIdx a (ppK j k) := by
  have e : ppK j k = pg 6 (mask 6) (rowsOf 6 PP j) k := by
    unfold ppK
    have hb : Nat.blt k 64 = true := Nat.ble_eq_true_of_le hk
    rw [hb]
  have e2 : Nat.land (Nat.shiftRight (rowsOf 6 PP j) (6 * k)) 63 = ppK j k := by
    rw [e]
    rfl
  have hb : ppK j k < 64 := by
    rw [← e2]
    change _ &&& (2 ^ 6 - 1) < 2 ^ 6
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by norm_num)
  unfold t25G
  rw [e2]
  unfold fIdx packEntry
  change (fTable >>> (64 * a) &&& (2 ^ 64 - 1)) >>> ppK j k &&& 1 =
    fTable >>> (1 * (64 * a + ppK j k)) % 2 ^ 1
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.one_mul, Nat.pow_one, Nat.and_one_is_mod,
    Nat.shiftRight_add]
  simp only [Nat.shiftRight_eq_div_pow]
  rw [show (2 : ℕ) ^ 64 = 2 ^ ppK j k * 2 ^ (64 - ppK j k) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]

theorem t25_lane_div (S k : ℕ) :
    Nat.land (Nat.shiftRight S (Nat.mul 12 k)) 4095 = S / 4096 ^ k % 4096 := by
  have e : Nat.land (Nat.shiftRight S (Nat.mul 12 k)) 4095 = S >>> (12 * k) % 2 ^ 12 :=
    Nat.and_two_pow_sub_one_eq_mod _ 12
  rw [e, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem t25Sum_lane (h k : ℕ) (hk : k < 64) :
    Nat.land (Nat.shiftRight (t25Sum h) (Nat.mul 12 k)) 4095 = FSumG ppK ihK h k := by
  have hs : t25Sum h = t25Enc (fun k => ((List.range 1485).map fun i =>
      t25G (Nat.land (Nat.shiftRight fTable (Nat.mul 64 (ppK i h))) (nat_lit 18446744073709551615))
        (rowsOf 6 PP (ihK i h)) (6 * k)).sum) 64 := by
    unfold t25Sum
    rw [PK.foldN_eq, t25_foldr_add, Nat.zero_add]
    simp only [t25Lanes_eq]
    exact t25Enc_sum (fun i k => t25G
      (Nat.land (Nat.shiftRight fTable (Nat.mul 64 (ppK i h))) (nat_lit 18446744073709551615))
      (rowsOf 6 PP (ihK i h)) (6 * k)) 64 1485
  rw [t25_lane_div, hs, t25Enc_lane ?hc k hk]
  · unfold FSumG
    exact congrArg List.sum (List.map_congr_left fun i _ => t25_bit _ _ k hk)
  · intro j _
    exact lt_of_le_of_lt (t25_sum_le _ (fun i => t25G_le _ _ _) 1485) (by norm_num)

theorem fTRL_spec {h : ℕ} (hf : fTRL h = true) {k : ℕ} (hk : k < 64) :
    ((FSumG ppK ihK h k + muIdx h + muIdx k + muIdx (mIdx h k)) % 2 == fIdx h k) = true := by
  unfold fTRL at hf
  rw [PK.strictB_eq] at hf
  unfold t25Row at hf
  have h3 := Nat.eq_of_beq_eq_true (allN_spec hf k hk)
  rw [t25Sum_lane h k hk] at h3
  exact beq_iff_eq.2 h3

theorem tr_all_range {n : Nat} {f : Nat → Bool} :
    (List.range n).all f = true ↔ ∀ i < n, f i = true := by
  simp [List.all_eq_true, List.mem_range]

theorem transC : transferCheck = true := by
  rw [transferCheck_eq, tp_eq, tih_eq]
  refine tr_all_range.2 fun h hh => tr_all_range.2 fun k hk => ?_
  exact fTRL_spec (CFSG.KC.Co3Bfs.cover_of_blocks (by decide) (by decide) T25TRL.all h hh) hk

end CertificateChecks.KernelM12T

end
