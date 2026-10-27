module

public import Certificates.Kernel.J2Cover.M22LamN
public import Certificates.Kernel.J2Cover.M22Tr
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Models
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models

private theorem strictN_lam (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem strictB_lam (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem bAnd_lam {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private theorem brec_ite (c : Bool) :
    Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 128) c = if c = true then 128 else 0 := by
  cases c <;> rfl

theorem mask_pow (w : Nat) : mask w = 2 ^ w - 1 := by
  change (1 <<< w) - 1 = 2 ^ w - 1
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem testBit_pg {w P x c : Nat} (hc : c < w) :
    (pg w (mask w) P x).testBit c = P.testBit (w * x + c) := by
  change ((P >>> (w * x)) &&& mask w).testBit c = _
  rw [mask_pow, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  simp [hc]

theorem testBit_fld1 (x o : Nat) : (Nat.land (Nat.shiftRight x o) (nat_lit 1)).testBit 0 = x.testBit o := by
  change ((x >>> o) &&& 1).testBit 0 = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  simp

theorem lane_lo {v : Nat} (c : Bool) (hv : v < 128) :
    Nat.land (v + if c = true then 128 else 0) (nat_lit 127) = v := by
  change (v + if c = true then 128 else 0) &&& (2 ^ 7 - 1) = v
  rw [Nat.and_two_pow_sub_one_eq_mod]
  cases c <;> simp <;> omega

theorem lane_hi {v : Nat} (c : Bool) (hv : v < 128) :
    (Nat.shiftRight (v + if c = true then 128 else 0) (nat_lit 7)).testBit 0 = c := by
  change ((v + if c = true then 128 else 0) >>> 7).testBit 0 = c
  rw [Nat.shiftRight_eq_div_pow]
  have e : (2 : Nat) ^ 7 = 128 := rfl
  rw [e]
  cases c
  · have h0 : (v + if false = true then 128 else 0) / 128 = 0 := by simp; omega
    rw [h0]
    rfl
  · have h1 : (v + if true = true then 128 else 0) / 128 = 1 := by simp; omega
    rw [h1]
    rfl

theorem testBit_nxor (x y i : Nat) : (Nat.xor x y).testBit i = (x.testBit i ^^ y.testBit i) :=
  Nat.testBit_xor x y i

theorem mtK_lt (a d : Nat) : mtK a d < 128 := by
  unfold mtK
  cases Nat.blt a 128
  · exact Nat.zero_lt_succ _
  · exact Nat.and_lt_two_pow (n := 7) _ (by decide)

theorem pg7_lt (P i : Nat) : pg 7 (mask 7) P i < 128 := by
  unfold pg
  exact Nat.and_lt_two_pow (n := 7) _ (by decide)

theorem bi_spec {a : Nat} (ha : a < 128) :
    fld(LTP 2, Nat.shiftLeft a (nat_lit 3), nat_lit 255) = btK a ∧
      fld(LTP 3, Nat.shiftLeft a (nat_lit 3), nat_lit 255) = itK a ∧ itK a < 128 := by
  have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) ch10022BI.all a ha
  unfold fBIP fBI at h
  obtain ⟨h1, h⟩ := bAnd_lam h
  obtain ⟨h2, h3⟩ := bAnd_lam h
  have e2 := Nat.eq_of_beq_eq_true h2
  refine ⟨Nat.eq_of_beq_eq_true h1, e2, ?_⟩
  rw [← e2]
  exact Nat.le_of_ble_eq_true h3

theorem si_spec {i : Nat} (hi : i < 4725) :
    pg 13 (mask 13) ACP i < 128 ∧ fld(LTP 1, Nat.shiftLeft i (nat_lit 3), nat_lit 255) =
      itK (pg 13 (mask 13) ACP i) +
        if (fRK (itK (pg 13 (mask 13) ACP i))).testBit (pg 13 (mask 13) ACP i) = true then 128
          else 0 := by
  have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) ch10022SI.all i hi
  unfold fSIP fSI at h
  rw [strictB_lam, strictB_lam] at h
  obtain ⟨h1, h2⟩ := bAnd_lam h
  have hs : pg 13 (mask 13) ACP i < 128 := Nat.le_of_ble_eq_true h1
  refine ⟨hs, ?_⟩
  rw [(bi_spec hs).2.1, brec_ite] at h2
  exact Nat.eq_of_beq_eq_true h2

theorem ac_lt (q : Nat) : pg 13 (mask 13) ACP q < 128 := by
  by_cases hq : q < 4725
  · exact (si_spec hq).1
  · rw [pg_beyond kACP (by omega)]
    omega

theorem lt_spec {x y : Nat} (hx : x < 128) (hy : y < 128) :
    fld(LTP 0, Nat.add (Nat.shiftLeft x (nat_lit 10)) (Nat.shiftLeft y (nat_lit 3)), nat_lit 255) =
      mtK x (btK y) + if (lamBit y ^^ (fRK x).testBit (btK y)) = true then 128 else 0 := by
  have hm : 128 * x + y < 16384 := by omega
  have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) ch10022LT.all (128 * x + y) hm
  have e1 : Nat.shiftRight (128 * x + y) (nat_lit 7) = x := by
    change (128 * x + y) >>> 7 = x
    rw [Nat.shiftRight_eq_div_pow]
    have e : (2 : Nat) ^ 7 = 128 := rfl
    rw [e]
    omega
  have e2 : Nat.land (128 * x + y) (nat_lit 127) = y := by
    change (128 * x + y) &&& (2 ^ 7 - 1) = y
    rw [Nat.and_two_pow_sub_one_eq_mod]
    have e : (2 : Nat) ^ 7 = 128 := rfl
    rw [e]
    omega
  have e3 : Nat.shiftLeft (128 * x + y) (nat_lit 3) =
      Nat.add (Nat.shiftLeft x (nat_lit 10)) (Nat.shiftLeft y (nat_lit 3)) := by
    change (128 * x + y) <<< 3 = (x <<< 10) + (y <<< 3)
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have e : (2 : Nat) ^ 3 = 8 := rfl
    have e' : (2 : Nat) ^ 10 = 1024 := rfl
    rw [e, e']
    ring
  unfold fLTP fLT at h
  rw [e1, e2, e3] at h
  beta_reduce at h
  rw [strictB_lam, (bi_spec hy).1, brec_ite] at h
  exact Nat.eq_of_beq_eq_true h

theorem stL_bit {i p : Nat} (q : Nat) (hi : i < 4725) (hp : p < 128) :
    (stL (LTP 0) (LTP 1) FRP ACP i p q).testBit 0 =
      (bitR fRK (itK (pg 13 (mask 13) ACP i)) (pg 13 (mask 13) ACP i) ^^ lamBit p ^^
        bitR fRK (itK (pg 13 (mask 13) ACP i)) (btK p) ^^
          bitR fRK (mtK (itK (pg 13 (mask 13) ACP i)) (btK p)) (pg 13 (mask 13) ACP q)) := by
  obtain ⟨hs, hS⟩ := si_spec hi
  have hsi : itK (pg 13 (mask 13) ACP i) < 128 := (bi_spec hs).2.2
  have hc := ac_lt q
  have hh := mtK_lt (itK (pg 13 (mask 13) ACP i)) (btK p)
  unfold stL
  rw [strictN_lam]
  beta_reduce
  rw [hS, lane_lo _ hsi, strictN_lam]
  beta_reduce
  rw [lt_spec hsi hp, lane_lo _ hh, testBit_nxor, testBit_nxor, lane_hi _ hsi, lane_hi _ hh,
    testBit_fld1]
  have e : Nat.add (Nat.shiftLeft (mtK (itK (pg 13 (mask 13) ACP i)) (btK p)) (nat_lit 7))
      (pg 13 (mask 13) ACP q) = 128 * mtK (itK (pg 13 (mask 13) ACP i)) (btK p) +
        pg 13 (mask 13) ACP q := by
    change (mtK (itK (pg 13 (mask 13) ACP i)) (btK p) <<< 7) + pg 13 (mask 13) ACP q = _
    rw [Nat.shiftLeft_eq]
    have e7 : (2 : Nat) ^ 7 = 128 := rfl
    rw [e7, Nat.mul_comm]
  have hb : bitR fRK (mtK (itK (pg 13 (mask 13) ACP i)) (btK p)) (pg 13 (mask 13) ACP q) =
      FRP.testBit (128 * mtK (itK (pg 13 (mask 13) ACP i)) (btK p) + pg 13 (mask 13) ACP q) := by
    unfold bitR fRK
    exact testBit_pg hc
  rw [e, ← hb]
  unfold bitR
  simp only [Bool.xor_assoc]

theorem xr4725_congr {p q : Nat → Bool} (h : ∀ i < 4725, p i = q i) : xr4725 p = xr4725 q := by
  unfold xr4725
  have h1 : ∀ k < 73, xorR p (64 * k) 64 = xorR q (64 * k) 64 :=
    fun k hk => xorR_congr 64 fun l hl => h _ (by omega)
  rw [xorR_congr (p := fun k => xorR p (64 * k) 64) (q := fun k => xorR q (64 * k) 64) 73
    (fun l hl => h1 _ (by omega)), xorR_congr 53 (fun l hl => h _ (by omega))]

end CertificateChecks.KernelJ2Cover

end
