module

public import Certificates.Kernel.RouteP.Y332.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.SliceRange
public import Mathlib

#kc_repo #kc_ktree CFSG.KD.RouteP.Y332Lv R "Certificates/Kernel/RouteP/Y332/data/ylev.bin" 196608 4
  9240576 15940732248755539477

public section

namespace CFSG.KD.RouteP

@[expose] noncomputable def ybase9 (j : Nat) : Bool := ybase (j + 9)

@[expose] noncomputable def nkY30 (j : Nat) : Bool := nkY (j + 30)

end CFSG.KD.RouteP

#kc_slice_range CFSG.KD.RouteP.yck CFSG.KD.RouteP.Y332Ck.y 0 940
#kc_slice_range CFSG.KD.RouteP.yfix CFSG.KD.RouteP.Y332Ck.f 0 18
#kc_slice_range CFSG.KD.RouteP.ybase9 CFSG.KD.RouteP.Y332Ck.b 0 62
#kc_slice_range CFSG.KD.RouteP.nkY30 CFSG.KD.RouteP.Y332Ck.n 0 82

namespace CFSG.KD.RouteP.Y332Lv

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.RouteP CFSG.KD.RouteP

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem letB_eq (v : Nat) (f : Nat → Bool) : letB v f = f v := by cases v <;> rfl

theorem closeS_one {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {gens : List Int} {n a b c : Nat}
    (h : Nat.beq (roundS NW KA KB gens a) b = true) (hc : closeS NW KA KB gens n b = c) :
    closeS NW KA KB gens (n + 1) a = c := by
  change strictN (roundS NW KA KB gens a) (closeS NW KA KB gens n) = c
  rw [strictN_eq, Nat.eq_of_beq_eq_true h]
  exact hc

theorem closeS_zero (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (gens : List Int) (a : Nat) :
    closeS NW KA KB gens 0 a = a := rfl

@[expose] noncomputable def yBlk (x h : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul h (nat_lit 4096)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 4096)) (nat_lit 1))

@[expose] noncomputable def pcountY (x hi : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun h ih => Nat.add (strictN (yBlk x h) (fun y =>
    Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add (nIf(Nat.blt (Nat.add (Nat.shiftLeft h 6) l) 24576,
        pc64 (fld(y, Nat.mul l 64, nat_lit 18446744073709551615)), 0)) ih2) 64)) ih) hi

theorem testBit_onesY (w i : Nat) : (Nat.sub (Nat.shiftLeft 1 w) 1).testBit i = decide (i < w) := by
  change (1 <<< w - 1).testBit i = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]

theorem fld_yBlk (x h l : Nat) (hl : l < 64) :
    fld(x, Nat.mul (Nat.add (Nat.shiftLeft h 6) l) (nat_lit 64), nat_lit 18446744073709551615) =
      fld(yBlk x h, Nat.mul l 64, nat_lit 18446744073709551615) := by
  have r : (nat_lit 18446744073709551615 : Nat) = 2 ^ 64 - 1 := rfl
  unfold yBlk
  rw [r]
  apply Nat.eq_of_testBit_eq
  intro i
  change (x >>> ((h <<< 6 + l) * 64) &&& (2 ^ 64 - 1)).testBit i =
    ((((x >>> (h * 4096)) &&& (Nat.sub (Nat.shiftLeft 1 4096) 1)) >>> (l * 64)) &&&
      (2 ^ 64 - 1)).testBit i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, Nat.testBit_and, testBit_onesY, Nat.testBit_shiftRight,
    Nat.shiftLeft_eq]
  by_cases hi : i < 64
  · have e : (h * 2 ^ 6 + l) * 64 + i = h * 4096 + (l * 64 + i) := by ring
    rw [e, decide_eq_true hi, decide_eq_true (by omega : l * 64 + i < 4096), Bool.and_true,
      Bool.and_true]
  · rw [decide_eq_false hi, Bool.and_false, Bool.and_false]

theorem pcountY_inner (x h : Nat) : ∀ n, n ≤ 64 →
    (Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add ((fun i => nIf(Nat.blt i (nat_lit 24576), (fun c => pc64 (fld(x,
        Nat.mul c (nat_lit 64), nat_lit 18446744073709551615))) i, 0))
        (Nat.add (Nat.shiftLeft h 6) l)) ih2) n : Nat) =
    Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add (nIf(Nat.blt (Nat.add (Nat.shiftLeft h 6) l) 24576,
        pc64 (fld(yBlk x h, Nat.mul l 64, nat_lit 18446744073709551615)), 0)) ih2) n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    change Nat.add _ _ = Nat.add _ _
    rw [ih (by omega)]
    beta_reduce
    rw [fld_yBlk x h n (by omega)]

theorem pcount_eq_pcountY (x : Nat) : pcount x = pcountY x (nat_lit 384) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0 (fun h ih => Nat.add (
      Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
        Nat.add ((fun i => nIf(Nat.blt i (nat_lit 24576), (fun c => pc64 (fld(x,
          Nat.mul c (nat_lit 64), nat_lit 18446744073709551615))) i, 0))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) ih) n : Nat) =
      Nat.rec (motive := fun _ => Nat) 0 (fun h ih => Nat.add (strictN (yBlk x h) (fun y =>
        Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
          Nat.add (nIf(Nat.blt (Nat.add (Nat.shiftLeft h 6) l) 24576,
            pc64 (fld(y, Nat.mul l 64, nat_lit 18446744073709551615)), 0)) ih2) 64)) ih) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change Nat.add _ _ = Nat.add _ _
      rw [ih, strictN_eq, pcountY_inner x n 64 le_rfl]
  have e1 : pcount x = sumBelow (nat_lit 24576) (nat_lit 384)
      (fun c => pc64 (fld(x, Nat.mul c (nat_lit 64), nat_lit 18446744073709551615))) := rfl
  have e2 : ∀ n, sumBelow (nat_lit 24576) n
      (fun c => pc64 (fld(x, Nat.mul c (nat_lit 64), nat_lit 18446744073709551615))) =
      pcountY x n := key
  rw [e1, e2]

@[expose] def bitCntY (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bitCntY f n + f n

theorem bitCntY_add (f : Nat → Nat) (a : Nat) :
    ∀ b, bitCntY f (a + b) = bitCntY f a + bitCntY (fun x => f (a + x)) b
  | 0 => rfl
  | b + 1 => by rw [← Nat.add_assoc, bitCntY, bitCntY, bitCntY_add f a b, Nat.add_assoc]

theorem bitCntY_congr {f g : Nat → Nat} : ∀ n, (∀ i < n, f i = g i) → bitCntY f n = bitCntY g n
  | 0, _ => rfl
  | n + 1, h => by rw [bitCntY, bitCntY, bitCntY_congr n (fun i hi => h i (by omega)), h n (by omega)]

theorem bitCntY_zero_fun {f : Nat → Nat} : ∀ n, (∀ i < n, f i = 0) → bitCntY f n = 0
  | 0, _ => rfl
  | n + 1, h => by rw [bitCntY, bitCntY_zero_fun n (fun i hi => h i (by omega)), h n (by omega)]

theorem bitCntY_mul (f : Nat → Nat) (k : Nat) :
    ∀ n, bitCntY f (k * n) = bitCntY (fun c => bitCntY (fun i => f (k * c + i)) k) n
  | 0 => by rw [Nat.mul_zero]; rfl
  | n + 1 => by rw [Nat.mul_succ, bitCntY_add, bitCntY_mul f k n, bitCntY]

def cntWY (w : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, z => z % 2 ^ w + cntWY w n (z / 2 ^ w)

def okFY (w : Nat) : Nat → Nat → Prop
  | 0, _ => True
  | n + 1, z => z % 2 ^ w ≤ w ∧ okFY w n (z / 2 ^ w)

def geoWY (W : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + 2 ^ W * geoWY W n

noncomputable def rndY (w n z : Nat) : Nat :=
  (z &&& (geoWY (2 * w) n * (2 ^ w - 1))) + ((z >>> w) &&& (geoWY (2 * w) n * (2 ^ w - 1)))

@[expose] noncomputable def ySwM (N k : Nat) : Nat :=
  Nat.mul (Nat.div (Nat.sub (Nat.shiftLeft 1 N) 1)
    (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.add k 1))) 1))
    (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 k)) 1)

@[expose] noncomputable def ySwR (N k z : Nat) : Nat :=
  strictN (ySwM N k) (fun M =>
    Nat.add (Nat.land z M) (Nat.land (Nat.shiftRight z (Nat.shiftLeft 1 k)) M))

@[expose] noncomputable def ySwG (N r : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ z => z)
    (fun _ ih k z => strictN (ySwR N k z) (ih (Nat.add k 1))) r

theorem and_splitY {a b m : Nat} (x y : Nat) (ha : a < 2 ^ m) (hb : b < 2 ^ m) :
    (a + 2 ^ m * x) &&& (b + 2 ^ m * y) = (a &&& b) + 2 ^ m * (x &&& y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.add_comm a, Nat.add_comm b, Nat.add_comm (a &&& b), Nat.testBit_and,
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow a hb), Nat.testBit_and, Nat.testBit_and]
  by_cases hj : j < m <;> simp [hj]

theorem geoWY_mul (W : Nat) : ∀ n, geoWY W n * (2 ^ W - 1) = 2 ^ (W * n) - 1
  | 0 => by simp [geoWY]
  | n + 1 => by
    rw [geoWY, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, geoWY_mul W n, Nat.mul_succ, pow_add,
      Nat.mul_sub, Nat.mul_one, Nat.mul_comm (2 ^ (W * n))]
    have hp : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    have hq : 1 ≤ 2 ^ (W * n) := Nat.one_le_two_pow
    have hpq : 2 ^ W ≤ 2 ^ W * 2 ^ (W * n) := Nat.le_mul_of_pos_right _ hq
    omega

theorem addDivY {W s : Nat} (r : Nat) (hs : s < 2 ^ W) :
    (s + 2 ^ W * r) % 2 ^ W = s ∧ (s + 2 ^ W * r) / 2 ^ W = r := by
  refine ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs], ?_⟩
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos W), Nat.div_eq_of_lt hs, Nat.zero_add]

theorem rnd_specY (w : Nat) : ∀ n z, okFY w (2 * n) z →
    rndY w n z < 2 ^ (2 * w * n) ∧ cntWY (2 * w) n (rndY w n z) = cntWY w (2 * n) z ∧
      okFY (2 * w) n (rndY w n z)
  | 0, z, _ => by
    have e : rndY w 0 z = 0 := by
      unfold rndY
      rw [geoWY, Nat.zero_mul, Nat.and_zero, Nat.and_zero]
    rw [e]
    exact ⟨Nat.two_pow_pos _, rfl, trivial⟩
  | n + 1, z, hz => by
    have hww : w ≤ 2 * w := by omega
    have hb : 2 ^ w - 1 < 2 ^ (2 * w) :=
      lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos) (Nat.pow_le_pow_right (by omega) hww)
    have hM : geoWY (2 * w) (n + 1) * (2 ^ w - 1) =
        (2 ^ w - 1) + 2 ^ (2 * w) * (geoWY (2 * w) n * (2 ^ w - 1)) := by
      rw [geoWY, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    have hdv : 2 ^ w ∣ 2 ^ (2 * w) := Nat.pow_dvd_pow 2 hww
    have hA : ∀ y : Nat, y &&& (geoWY (2 * w) (n + 1) * (2 ^ w - 1)) =
        y % 2 ^ w + 2 ^ (2 * w) * (y / 2 ^ (2 * w) &&& (geoWY (2 * w) n * (2 ^ w - 1))) := by
      intro y
      have h := and_splitY (y / 2 ^ (2 * w)) (geoWY (2 * w) n * (2 ^ w - 1))
        (Nat.mod_lt y (Nat.two_pow_pos (2 * w))) hb
      rw [Nat.mod_add_div, ← hM, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ hdv] at h
      exact h
    have e2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e2] at hz
    obtain ⟨hz0, hz1, hz2⟩ := hz
    have hzz : z / 2 ^ w / 2 ^ w = z / 2 ^ (2 * w) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.two_mul]
    rw [hzz] at hz2
    have hsh : (z >>> w) / 2 ^ (2 * w) = (z / 2 ^ (2 * w)) >>> w := by
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
        Nat.div_div_eq_div_mul, Nat.mul_comm]
    have hR : rndY w (n + 1) z =
        (z % 2 ^ w + (z / 2 ^ w) % 2 ^ w) + 2 ^ (2 * w) * rndY w n (z / 2 ^ (2 * w)) := by
      unfold rndY
      rw [hA, hA, hsh, Nat.shiftRight_eq_div_pow z w]
      ring
    have hs2 : z % 2 ^ w + (z / 2 ^ w) % 2 ^ w < 2 ^ (2 * w) :=
      lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
    obtain ⟨i1, i2, i3⟩ := rnd_specY w n (z / 2 ^ (2 * w)) hz2
    obtain ⟨d1, d2⟩ := addDivY (rndY w n (z / 2 ^ (2 * w))) hs2
    rw [hR]
    refine ⟨?_, ?_, ?_⟩
    · have e3 : 2 ^ (2 * w * (n + 1)) = 2 ^ (2 * w) * 2 ^ (2 * w * n) := by ring
      rw [e3]
      calc _ < 2 ^ (2 * w) + 2 ^ (2 * w) * rndY w n (z / 2 ^ (2 * w)) := by omega
        _ = 2 ^ (2 * w) * (rndY w n (z / 2 ^ (2 * w)) + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ i1
    · rw [cntWY, d1, d2, i2, e2, cntWY, cntWY, hzz]
      ring
    · rw [okFY, d1, d2]
      exact ⟨by omega, i3⟩

theorem ySwR_eq (N k n z : Nat) (hN : N = 2 * 2 ^ k * n) :
    ySwR N k z = rndY (2 ^ k) n z := by
  unfold ySwR
  rw [strictN_eq]
  have hM : ySwM N k = geoWY (2 * 2 ^ k) n * (2 ^ 2 ^ k - 1) := by
    unfold ySwM
    change ((1 <<< N) - 1) / ((1 <<< (1 <<< (k + 1))) - 1) * ((1 <<< (1 <<< k)) - 1) = _
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
    have e : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [e]
    congr 1
    apply Nat.div_eq_of_eq_mul_left (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by positivity)))
    rw [geoWY_mul, hN]
  rw [hM]
  unfold rndY
  change Nat.land z _ + Nat.land (z >>> (1 <<< k)) _ = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  rfl

theorem ySwG_spec (N : Nat) : ∀ r k z, N = 2 ^ (k + r) → okFY (2 ^ k) (2 ^ r) z →
    (r = 0 → z < 2 ^ N) → ySwG N r k z = cntWY (2 ^ k) (2 ^ r) z
  | 0, k, z, hN, _, hz => by
    change z = z % 2 ^ 2 ^ k + 0
    rw [Nat.add_zero, Nat.mod_eq_of_lt]
    rw [Nat.add_zero] at hN
    rw [← hN]
    exact hz rfl
  | r + 1, k, z, hN, hok, _ => by
    change strictN (ySwR N k z) (ySwG N r (k + 1)) = _
    rw [strictN_eq, ySwR_eq N k (2 ^ r) z (by rw [hN]; ring)]
    have e1 : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
    rw [e1] at hok ⊢
    obtain ⟨i1, i2, i3⟩ := rnd_specY (2 ^ k) (2 ^ r) z hok
    have e2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [ySwG_spec N r (k + 1) _ (by rw [hN]; ring) (by rw [e2]; exact i3)
      (fun _ => by rw [hN]; convert i1 using 2; ring), e2, i2]

theorem okF1Y : ∀ n z, okFY 1 n z
  | 0, _ => trivial
  | n + 1, z => ⟨by have := Nat.mod_lt z (Nat.two_pow_pos 1); omega, okF1Y n _⟩

theorem cnt1Y : ∀ n z, cntWY 1 n z = bitCntY (fun q => if z.testBit q then 1 else 0) n
  | 0, _ => rfl
  | n + 1, z => by
    rw [cntWY, cnt1Y n, Nat.add_comm n 1, bitCntY_add]
    have e : bitCntY (fun q => if z.testBit q then 1 else 0) 1 =
        if z.testBit 0 then 1 else 0 := Nat.zero_add _
    rw [e, pow_one]
    congr 1
    · rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one z with h | h <;> simp [h]
    · exact bitCntY_congr n fun i _ => by rw [Nat.add_comm 1 i, Nat.testBit_succ]

theorem tb_yBlk (x h i : Nat) :
    (yBlk x h).testBit i = (decide (i < 4096) && x.testBit (h * 4096 + i)) := by
  unfold yBlk
  change ((x >>> (h * 4096)) &&& (Nat.sub (Nat.shiftLeft 1 4096) 1)).testBit i = _
  rw [Nat.testBit_and, testBit_onesY, Nat.testBit_shiftRight, Bool.and_comm]

theorem pc64_fldY (y l : Nat) :
    pc64 (fld(y, Nat.mul l 64, nat_lit 18446744073709551615)) =
      bitCntY (fun j => if y.testBit (64 * l + j) then 1 else 0) 64 := by
  have key : ∀ (z k : Nat), (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight z i) (nat_lit 1))) k : Nat) =
      bitCntY (fun i => if z.testBit i then 1 else 0) k := by
    intro z k
    induction k with
    | zero => rfl
    | succ k ih =>
      change Nat.add _ _ = _
      rw [ih, bitCntY, Nat.add_eq]
      congr 1
      have e : Nat.land (Nat.shiftRight z k) 1 = (z >>> k) % 2 := Nat.and_one_is_mod _
      have hb : z.testBit k = decide ((z >>> k) % 2 = 1) := by
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
      rw [e, hb]
      rcases Nat.mod_two_eq_zero_or_one (z >>> k) with h | h <;> rw [h] <;> rfl
  refine (key _ 64).trans (bitCntY_congr 64 fun j hj => ?_)
  have r : (nat_lit 18446744073709551615 : Nat) = 2 ^ 64 - 1 := rfl
  change (if ((y >>> (l * 64)) &&& nat_lit 18446744073709551615).testBit j then 1 else 0) = _
  rw [r, Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true hj, Bool.and_true,
    Nat.testBit_shiftRight, Nat.mul_comm l 64]

theorem blockY (y h : Nat) (hh : h < 384) : ∀ n, n ≤ 64 →
    (Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add (nIf(Nat.blt (Nat.add (Nat.shiftLeft h 6) l) 24576,
        pc64 (fld(y, Nat.mul l 64, nat_lit 18446744073709551615)), 0)) ih2) n : Nat) =
    bitCntY (fun c => bitCntY (fun j => if y.testBit (64 * c + j) then 1 else 0) 64) n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    change Nat.add _ _ = _
    rw [ih (by omega), bitCntY, Nat.add_eq, Nat.add_comm]
    congr 1
    have hg : Nat.blt (Nat.add (Nat.shiftLeft h 6) n) 24576 = true := by
      apply Nat.blt_eq.mpr
      change h <<< 6 + n < 24576
      rw [Nat.shiftLeft_eq]
      omega
    rw [hg]
    exact pc64_fldY y n

theorem pcountY_bits (x : Nat) : ∀ n, n ≤ 384 → pcountY x n =
    bitCntY (fun c => bitCntY (fun i => if x.testBit (4096 * c + i) then 1 else 0) 4096) n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    change Nat.add (strictN (yBlk x n) _) (pcountY x n) = _
    rw [ih (by omega), strictN_eq]
    rw [blockY (yBlk x n) n (by omega) 64 le_rfl, bitCntY, Nat.add_eq, Nat.add_comm]
    congr 1
    refine (bitCntY_mul (fun q => if (yBlk x n).testBit q then 1 else 0) 64 64).symm.trans ?_
    refine bitCntY_congr 4096 fun i hi => ?_
    rw [tb_yBlk, decide_eq_true hi, Bool.true_and, Nat.mul_comm n 4096]

theorem pcount_eq_swY (x : Nat) : pcount x = ySwG 2097152 21 0
    (Nat.land x (Nat.sub (Nat.shiftLeft 1 1572864) 1)) := by
  rw [pcount_eq_pcountY, pcountY_bits x 384 le_rfl]
  refine (bitCntY_mul (fun q => if x.testBit q then 1 else 0) 4096 384).symm.trans ?_
  rw [ySwG_spec 2097152 21 0 _ (by norm_num) (okF1Y _ _) (fun h => absurd h (by decide)),
    pow_zero, cnt1Y]
  have e : (2 : Nat) ^ 21 = 1572864 + 524288 := by norm_num
  have ht : ∀ i, (Nat.land x (Nat.sub (Nat.shiftLeft 1 1572864) 1)).testBit i =
      (x.testBit i && decide (i < 1572864)) := fun i => by
    change (x &&& Nat.sub (Nat.shiftLeft 1 1572864) 1).testBit i = _
    rw [Nat.testBit_and, testBit_onesY]
  have hz : bitCntY (fun i => if (Nat.land x (Nat.sub (Nat.shiftLeft 1 1572864) 1)).testBit
      (1572864 + i) then 1 else 0) 524288 = 0 := by
    refine bitCntY_zero_fun 524288 fun i _ => ?_
    rw [ht, decide_eq_false (by omega), Bool.and_false]
    rfl
  rw [e, bitCntY_add, hz, Nat.add_zero]
  exact bitCntY_congr 1572864 fun i hi => by
    rw [ht, decide_eq_true hi, Bool.and_true]

@[irreducible] noncomputable def cntOK (S m : Nat) : Bool :=
  Nat.beq (ySwG 2097152 21 0 (Nat.land (Nat.land S ptsS) (Nat.sub (Nat.shiftLeft 1 1572864) 1))) m

theorem orbOK_of {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {gens : List Int} {x n m S : Nat}
    (h0 : closeS NW KA KB gens n (single x) = S) (hc : closedS NW KA KB gens S = true)
    (hm : cntOK S m = true) : orbOK NW KA KB gens x n m = true := by
  unfold cntOK at hm
  rw [← pcount_eq_swY] at hm
  unfold orbOK
  rw [letB_eq, h0, hc, hm]
  rfl

theorem s0_0 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (single 15)) (R 0) = true := by
  quickRfl

theorem s0_1 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 0)) (R 1) = true := by
  quickRfl

theorem s0_2 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 1)) (R 2) = true := by
  quickRfl

theorem s0_3 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 2)) (R 3) = true := by
  quickRfl

theorem s0_4 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 3)) (R 4) = true := by
  quickRfl

theorem s0_5 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 4)) (R 5) = true := by
  quickRfl

theorem s0_6 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 5)) (R 6) = true := by
  quickRfl

theorem s0_7 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 6)) (R 7) = true := by
  quickRfl

theorem s0_8 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 7)) (R 8) = true := by
  quickRfl

theorem s0_9 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 8)) (R 9) = true := by
  quickRfl

theorem s0_10 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 9)) (R 10) = true := by
  quickRfl

theorem s0_11 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 10)) (R 11) = true := by
  quickRfl

theorem s0_12 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 11)) (R 12) = true := by
  quickRfl

theorem s0_13 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 12)) (R 13) = true := by
  quickRfl

theorem s0_14 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 13)) (R 14) = true := by
  quickRfl

theorem s0_15 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 14)) (R 15) = true := by
  quickRfl

theorem s0_16 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 15)) (R 16) = true := by
  quickRfl

theorem s0_17 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 16)) (R 17) = true := by
  quickRfl

theorem s0_18 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 17)) (R 18) = true := by
  quickRfl

theorem s0_19 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 18)) (R 19) = true := by
  quickRfl

theorem s0_20 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 19)) (R 20) = true := by
  quickRfl

theorem s0_21 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 20)) (R 21) = true := by
  quickRfl

theorem s0_22 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 21)) (R 22) = true := by
  quickRfl

theorem s0_23 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 22)) (R 23) = true := by
  quickRfl

theorem s0_24 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 23)) (R 24) = true := by
  quickRfl

theorem s0_25 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 24)) (R 25) = true := by
  quickRfl

theorem s0_26 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 25)) (R 26) = true := by
  quickRfl

theorem s0_27 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 26)) (R 27) = true := by
  quickRfl

theorem s0_28 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 27)) (R 28) = true := by
  quickRfl

theorem s0_29 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 28)) (R 29) = true := by
  quickRfl

theorem s0_30 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 29)) (R 30) = true := by
  quickRfl

theorem s0_31 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 30)) (R 31) = true := by
  quickRfl

theorem s0_32 : Nat.beq (roundS NWY KAY KBY (yLetters 0) (R 31)) (R 32) = true := by
  quickRfl

theorem c0 : closedS NWY KAY KBY (yLetters 0) (R 32) = true := by quickRfl

theorem m0 : cntOK (R 32) 28160 = true := by quickRfl

theorem lv0 : orbOK NWY KAY KBY (yLetters 0) 15 33 28160 = true :=
  orbOK_of (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (x := 15) (n := 33)
    (m := 28160) (S := R 32)
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 32)
    (a := single 15) (b := R 0) (c := R 32) s0_0
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 31)
    (a := R 0) (b := R 1) (c := R 32) s0_1
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 30)
    (a := R 1) (b := R 2) (c := R 32) s0_2
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 29)
    (a := R 2) (b := R 3) (c := R 32) s0_3
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 28)
    (a := R 3) (b := R 4) (c := R 32) s0_4
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 27)
    (a := R 4) (b := R 5) (c := R 32) s0_5
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 26)
    (a := R 5) (b := R 6) (c := R 32) s0_6
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 25)
    (a := R 6) (b := R 7) (c := R 32) s0_7
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 24)
    (a := R 7) (b := R 8) (c := R 32) s0_8
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 23)
    (a := R 8) (b := R 9) (c := R 32) s0_9
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 22)
    (a := R 9) (b := R 10) (c := R 32) s0_10
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 21)
    (a := R 10) (b := R 11) (c := R 32) s0_11
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 20)
    (a := R 11) (b := R 12) (c := R 32) s0_12
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 19)
    (a := R 12) (b := R 13) (c := R 32) s0_13
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 18)
    (a := R 13) (b := R 14) (c := R 32) s0_14
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 17)
    (a := R 14) (b := R 15) (c := R 32) s0_15
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 16)
    (a := R 15) (b := R 16) (c := R 32) s0_16
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 15)
    (a := R 16) (b := R 17) (c := R 32) s0_17
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 14)
    (a := R 17) (b := R 18) (c := R 32) s0_18
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 13)
    (a := R 18) (b := R 19) (c := R 32) s0_19
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 12)
    (a := R 19) (b := R 20) (c := R 32) s0_20
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 11)
    (a := R 20) (b := R 21) (c := R 32) s0_21
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 10)
    (a := R 21) (b := R 22) (c := R 32) s0_22
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 9)
    (a := R 22) (b := R 23) (c := R 32) s0_23
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 8)
    (a := R 23) (b := R 24) (c := R 32) s0_24
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 7)
    (a := R 24) (b := R 25) (c := R 32) s0_25
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 6)
    (a := R 25) (b := R 26) (c := R 32) s0_26
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 5)
    (a := R 26) (b := R 27) (c := R 32) s0_27
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 4)
    (a := R 27) (b := R 28) (c := R 32) s0_28
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 3)
    (a := R 28) (b := R 29) (c := R 32) s0_29
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 2)
    (a := R 29) (b := R 30) (c := R 32) s0_30
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 1)
    (a := R 30) (b := R 31) (c := R 32) s0_31
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 0) (n := 0)
    (a := R 31) (b := R 32) (c := R 32) s0_32
    (closeS_zero NWY KAY KBY (yLetters 0) (R 32))))))))))))))))))))))))))))))))))) c0 m0

theorem s1_0 : Nat.beq (roundS NWY KAY KBY (yLetters 1) (single 18)) (R 33) = true := by
  quickRfl

theorem s1_1 : Nat.beq (roundS NWY KAY KBY (yLetters 1) (R 33)) (R 34) = true := by
  quickRfl

theorem s1_2 : Nat.beq (roundS NWY KAY KBY (yLetters 1) (R 34)) (R 35) = true := by
  quickRfl

theorem s1_3 : Nat.beq (roundS NWY KAY KBY (yLetters 1) (R 35)) (R 36) = true := by
  quickRfl

theorem s1_4 : Nat.beq (roundS NWY KAY KBY (yLetters 1) (R 36)) (R 37) = true := by
  quickRfl

theorem c1 : closedS NWY KAY KBY (yLetters 1) (R 37) = true := by quickRfl

theorem m1 : cntOK (R 37) 3159 = true := by quickRfl

theorem lv1 : orbOK NWY KAY KBY (yLetters 1) 18 5 3159 = true :=
  orbOK_of (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 1) (x := 18) (n := 5)
    (m := 3159) (S := R 37)
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 1) (n := 4)
    (a := single 18) (b := R 33) (c := R 37) s1_0
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 1) (n := 3)
    (a := R 33) (b := R 34) (c := R 37) s1_1
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 1) (n := 2)
    (a := R 34) (b := R 35) (c := R 37) s1_2
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 1) (n := 1)
    (a := R 35) (b := R 36) (c := R 37) s1_3
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 1) (n := 0)
    (a := R 36) (b := R 37) (c := R 37) s1_4
    (closeS_zero NWY KAY KBY (yLetters 1) (R 37))))))) c1 m1

theorem s2_0 : Nat.beq (roundS NWY KAY KBY (yLetters 2) (single 27)) (R 38) = true := by
  quickRfl

theorem s2_1 : Nat.beq (roundS NWY KAY KBY (yLetters 2) (R 38)) (R 39) = true := by
  quickRfl

theorem s2_2 : Nat.beq (roundS NWY KAY KBY (yLetters 2) (R 39)) (R 40) = true := by
  quickRfl

theorem c2 : closedS NWY KAY KBY (yLetters 2) (R 40) = true := by quickRfl

theorem m2 : cntOK (R 40) 288 = true := by quickRfl

theorem lv2 : orbOK NWY KAY KBY (yLetters 2) 27 3 288 = true :=
  orbOK_of (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 2) (x := 27) (n := 3)
    (m := 288) (S := R 40)
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 2) (n := 2)
    (a := single 27) (b := R 38) (c := R 40) s2_0
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 2) (n := 1)
    (a := R 38) (b := R 39) (c := R 40) s2_1
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 2) (n := 0)
    (a := R 39) (b := R 40) (c := R 40) s2_2
    (closeS_zero NWY KAY KBY (yLetters 2) (R 40))))) c2 m2

theorem s3_0 : Nat.beq (roundS NWY KAY KBY (yLetters 3) (single 30)) (R 41) = true := by
  quickRfl

theorem c3 : closedS NWY KAY KBY (yLetters 3) (R 41) = true := by quickRfl

theorem m3 : cntOK (R 41) 7 = true := by quickRfl

theorem lv3 : orbOK NWY KAY KBY (yLetters 3) 30 1 7 = true :=
  orbOK_of (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 3) (x := 30) (n := 1)
    (m := 7) (S := R 41)
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 3) (n := 0)
    (a := single 30) (b := R 41) (c := R 41) s3_0
    (closeS_zero NWY KAY KBY (yLetters 3) (R 41))) c3 m3

theorem s4_0 : Nat.beq (roundS NWY KAY KBY (yLetters 4) (single 3)) (R 42) = true := by
  quickRfl

theorem s4_1 : Nat.beq (roundS NWY KAY KBY (yLetters 4) (R 42)) (R 43) = true := by
  quickRfl

theorem c4 : closedS NWY KAY KBY (yLetters 4) (R 43) = true := by quickRfl

theorem m4 : cntOK (R 43) 12 = true := by quickRfl

theorem lv4 : orbOK NWY KAY KBY (yLetters 4) 3 2 12 = true :=
  orbOK_of (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 4) (x := 3) (n := 2)
    (m := 12) (S := R 43)
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 4) (n := 1)
    (a := single 3) (b := R 42) (c := R 43) s4_0
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 4) (n := 0)
    (a := R 42) (b := R 43) (c := R 43) s4_1
    (closeS_zero NWY KAY KBY (yLetters 4) (R 43)))) c4 m4

theorem s5_0 : Nat.beq (roundS NWY KAY KBY (yLetters 5) (single 6)) (R 44) = true := by
  quickRfl

theorem c5 : closedS NWY KAY KBY (yLetters 5) (R 44) = true := by quickRfl

theorem m5 : cntOK (R 44) 5 = true := by quickRfl

theorem lv5 : orbOK NWY KAY KBY (yLetters 5) 6 1 5 = true :=
  orbOK_of (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 5) (x := 6) (n := 1)
    (m := 5) (S := R 44)
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 5) (n := 0)
    (a := single 6) (b := R 44) (c := R 44) s5_0
    (closeS_zero NWY KAY KBY (yLetters 5) (R 44))) c5 m5

theorem s6_0 : Nat.beq (roundS NWY KAY KBY (yLetters 6) (single 9)) (R 45) = true := by
  quickRfl

theorem c6 : closedS NWY KAY KBY (yLetters 6) (R 45) = true := by quickRfl

theorem m6 : cntOK (R 45) 4 = true := by quickRfl

theorem lv6 : orbOK NWY KAY KBY (yLetters 6) 9 1 4 = true :=
  orbOK_of (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 6) (x := 9) (n := 1)
    (m := 4) (S := R 45)
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 6) (n := 0)
    (a := single 9) (b := R 45) (c := R 45) s6_0
    (closeS_zero NWY KAY KBY (yLetters 6) (R 45))) c6 m6

theorem s7_0 : Nat.beq (roundS NWY KAY KBY (yLetters 7) (single 12)) (R 46) = true := by
  quickRfl

theorem c7 : closedS NWY KAY KBY (yLetters 7) (R 46) = true := by quickRfl

theorem m7 : cntOK (R 46) 3 = true := by quickRfl

theorem lv7 : orbOK NWY KAY KBY (yLetters 7) 12 1 3 = true :=
  orbOK_of (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 7) (x := 12) (n := 1)
    (m := 3) (S := R 46)
    (closeS_one (NW := NWY) (KA := KAY) (KB := KBY) (gens := yLetters 7) (n := 0)
    (a := single 12) (b := R 46) (c := R 46) s7_0
    (closeS_zero NWY KAY KBY (yLetters 7) (R 46))) c7 m7

end CFSG.KD.RouteP.Y332Lv

namespace CFSG.KD.RouteP.Y332Ck

open CFSG.KD.RouteP

theorem l0 : ylev (nat_lit 0) = true := Y332Lv.lv0

theorem l1 : ylev (nat_lit 1) = true := Y332Lv.lv1

theorem l2 : ylev (nat_lit 2) = true := Y332Lv.lv2

theorem l3 : ylev (nat_lit 3) = true := Y332Lv.lv3

theorem l4 : ylev (nat_lit 4) = true := Y332Lv.lv4

theorem l5 : ylev (nat_lit 5) = true := Y332Lv.lv5

theorem l6 : ylev (nat_lit 6) = true := Y332Lv.lv6

theorem l7 : ylev (nat_lit 7) = true := Y332Lv.lv7

end CFSG.KD.RouteP.Y332Ck

end
