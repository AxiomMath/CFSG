module

public import Certificates.Kernel.RouteP.Data.Pres
public import Certificates.Kernel.RouteP.Data.Obj
public import Certificates.Data.Kernel.RouteP.Geom
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Mathlib

#kc_repo #kc_ktree CFSG.KD.RouteP.GeomLv R "Certificates/Kernel/RouteP/Geom/data/geom.bin" 196608 4
  26345472 17983003297635026719

public section

namespace CFSG.KD.RouteP.GeomLv

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.RouteP

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem letB_eq (v : Nat) (f : Nat → Bool) : letB v f = f v := by cases v <;> rfl

theorem andB_t {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  rw [ha, hb]
  rfl

theorem closeS_one {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {gens : List Int} {n a b c : Nat}
    (h : Nat.beq (roundS NW KA KB gens a) b = true) (hc : closeS NW KA KB gens n b = c) :
    closeS NW KA KB gens (n + 1) a = c := by
  change strictN (roundS NW KA KB gens a) (closeS NW KA KB gens n) = c
  rw [strictN_eq, Nat.eq_of_beq_eq_true h]
  exact hc

theorem closeS_zero (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (gens : List Int) (a : Nat) :
    closeS NW KA KB gens 0 a = a := rfl

theorem allI_of {f : Nat → Bool} : ∀ {n : Nat}, (∀ i < n, f i = true) → allI n f = true
  | 0, _ => rfl
  | n + 1, h => andB_t (h n (by omega)) (allI_of fun i hi => h i (by omega))

theorem lt7 {p : Nat → Prop} (h0 : p 0) (h1 : p 1) (h2 : p 2) (h3 : p 3) (h4 : p 4) (h5 : p 5)
    (h6 : p 6) : ∀ i < 7, p i := by
  intro i hi
  interval_cases i <;> assumption

@[expose] noncomputable def geoBlk (x h : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul h (nat_lit 4096)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 4096)) (nat_lit 1))

@[expose] noncomputable def pcountG (x hi : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun h ih => Nat.add (strictN (geoBlk x h) (fun y =>
    Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add (nIf(Nat.blt (Nat.add (Nat.shiftLeft h 6) l) 24576,
        pc64 (fld(y, Nat.mul l 64, nat_lit 18446744073709551615)), 0)) ih2) 64)) ih) hi

theorem testBit_onesG (w i : Nat) : (Nat.sub (Nat.shiftLeft 1 w) 1).testBit i = decide (i < w) := by
  change (1 <<< w - 1).testBit i = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]

theorem fld_geoBlk (x h l : Nat) (hl : l < 64) :
    fld(x, Nat.mul (Nat.add (Nat.shiftLeft h 6) l) (nat_lit 64), nat_lit 18446744073709551615) =
      fld(geoBlk x h, Nat.mul l 64, nat_lit 18446744073709551615) := by
  have r : (nat_lit 18446744073709551615 : Nat) = 2 ^ 64 - 1 := rfl
  unfold geoBlk
  rw [r]
  apply Nat.eq_of_testBit_eq
  intro i
  change (x >>> ((h <<< 6 + l) * 64) &&& (2 ^ 64 - 1)).testBit i =
    ((((x >>> (h * 4096)) &&& (Nat.sub (Nat.shiftLeft 1 4096) 1)) >>> (l * 64)) &&&
      (2 ^ 64 - 1)).testBit i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, Nat.testBit_and, testBit_onesG, Nat.testBit_shiftRight,
    Nat.shiftLeft_eq]
  by_cases hi : i < 64
  · have e : (h * 2 ^ 6 + l) * 64 + i = h * 4096 + (l * 64 + i) := by ring
    rw [e, decide_eq_true hi, decide_eq_true (by omega : l * 64 + i < 4096), Bool.and_true,
      Bool.and_true]
  · rw [decide_eq_false hi, Bool.and_false, Bool.and_false]

theorem pcountG_inner (x h : Nat) : ∀ n, n ≤ 64 →
    (Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add ((fun i => nIf(Nat.blt i (nat_lit 24576), (fun c => pc64 (fld(x,
        Nat.mul c (nat_lit 64), nat_lit 18446744073709551615))) i, 0))
        (Nat.add (Nat.shiftLeft h 6) l)) ih2) n : Nat) =
    Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add (nIf(Nat.blt (Nat.add (Nat.shiftLeft h 6) l) 24576,
        pc64 (fld(geoBlk x h, Nat.mul l 64, nat_lit 18446744073709551615)), 0)) ih2) n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    change Nat.add _ _ = Nat.add _ _
    rw [ih (by omega)]
    beta_reduce
    rw [fld_geoBlk x h n (by omega)]

theorem pcount_eq_pcountG (x : Nat) : pcount x = pcountG x (nat_lit 384) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0 (fun h ih => Nat.add (
      Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
        Nat.add ((fun i => nIf(Nat.blt i (nat_lit 24576), (fun c => pc64 (fld(x,
          Nat.mul c (nat_lit 64), nat_lit 18446744073709551615))) i, 0))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) ih) n : Nat) =
      Nat.rec (motive := fun _ => Nat) 0 (fun h ih => Nat.add (strictN (geoBlk x h) (fun y =>
        Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
          Nat.add (nIf(Nat.blt (Nat.add (Nat.shiftLeft h 6) l) 24576,
            pc64 (fld(y, Nat.mul l 64, nat_lit 18446744073709551615)), 0)) ih2) 64)) ih) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change Nat.add _ _ = Nat.add _ _
      rw [ih, strictN_eq, pcountG_inner x n 64 le_rfl]
  have e1 : pcount x = sumBelow (nat_lit 24576) (nat_lit 384)
      (fun c => pc64 (fld(x, Nat.mul c (nat_lit 64), nat_lit 18446744073709551615))) := rfl
  have e2 : ∀ n, sumBelow (nat_lit 24576) n
      (fun c => pc64 (fld(x, Nat.mul c (nat_lit 64), nat_lit 18446744073709551615))) =
      pcountG x n := key
  rw [e1, e2]

@[irreducible] noncomputable def cntOK (x m : Nat) : Bool := Nat.beq (pcountG x (nat_lit 384)) m

theorem cnt_of {x m : Nat} (h : cntOK x m = true) : Nat.beq (pcount x) m = true := by
  unfold cntOK at h
  rw [pcount_eq_pcountG]
  exact h

theorem geomSetOK_of {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {NWO : Nat → Nat → Nat}
    {KAO KBO : Nat → Nat} {zg ag : List Int} {a0 a1 a2 a3 a4 a5 a6 A : Nat} {S : Nat → Nat}
    (h0 : zS NW KA KB zg 0 = a0) (h1 : zS NW KA KB zg 1 = a1) (h2 : zS NW KA KB zg 2 = a2)
    (h3 : zS NW KA KB zg 3 = a3) (h4 : zS NW KA KB zg 4 = a4) (h5 : zS NW KA KB zg 5 = a5)
    (h6 : zS NW KA KB zg 6 = a6) (hA : closeS NWO KAO KBO ag 10 (single 99705) = A)
    (hS : sel7 a0 a1 a2 a3 a4 a5 a6 = S)
    (hcl : ∀ i < 7, closedS NW KA KB zg (S i) = true)
    (hm : ∀ i < 7, cntOK (Nat.land (S i) ptsS) (gSize i) = true)
    (hdc : andB (allI 7 fun i => allI 7 fun j => orB (Nat.beq i j) (Nat.beq (Nat.land (S i) (S j)) 0))
      (Nat.beq (Nat.land (lorI S 7) ptsS) ptsS) = true)
    (hd : ∀ i < 7, distSetOK NW KA KB S i = true)
    (hAc : closedS NWO KAO KBO ag A = true) (hAm : cntOK (Nat.land A ptsS) 3510 = true)
    (hr : andB (allI 3 fun t => andB (ptOK NWO KAO KBO [((t + 7 : Nat) : Int)] 0 0)
        (ptOK NWO KAO KBO [((t + 7 : Nat) : Int)] 1479 1479))
      (letB (Nat.land (imgS NWO KAO KBO (-10) (S 1)) (S 1)) fun X => Nat.beq (Nat.land X A) X) = true) :
    geomSetOK NW KA KB NWO KAO KBO zg ag = true := by
  unfold geomSetOK
  simp only [letB_eq]
  rw [h0, h1, h2, h3, h4, h5, h6, hA, hS]
  exact andB_t (andB_t (allI_of fun i hi => andB_t (hcl i hi) (cnt_of (hm i hi))) hdc)
    (andB_t (allI_of hd) (andB_t (andB_t hAc (cnt_of hAm)) hr))

theorem s1_0 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (single 1479)) (R 0) = true := by
  quickRfl

theorem s1_1 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 0)) (R 1) = true := by
  quickRfl

theorem s1_2 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 1)) (R 2) = true := by
  quickRfl

theorem s1_3 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 2)) (R 3) = true := by
  quickRfl

theorem s1_4 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 3)) (R 4) = true := by
  quickRfl

theorem s1_5 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 4)) (R 5) = true := by
  quickRfl

theorem s1_6 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 5)) (R 6) = true := by
  quickRfl

theorem s1_7 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 6)) (R 7) = true := by
  quickRfl

theorem s1_8 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 7)) (R 8) = true := by
  quickRfl

theorem s1_9 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 8)) (R 9) = true := by
  quickRfl

theorem s1_10 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 9)) (R 10) = true := by
  quickRfl

theorem s1_11 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 10)) (R 11) = true := by
  quickRfl

theorem s1_12 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 11)) (R 12) = true := by
  quickRfl

theorem s1_13 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 12)) (R 13) = true := by
  quickRfl

theorem s1_14 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 13)) (R 14) = true := by
  quickRfl

theorem s1_15 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 14)) (R 15) = true := by
  quickRfl

theorem s1_16 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 15)) (R 16) = true := by
  quickRfl

theorem s1_17 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 16)) (R 17) = true := by
  quickRfl

theorem s1_18 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 17)) (R 18) = true := by
  quickRfl

theorem s1_19 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 18)) (R 19) = true := by
  quickRfl

theorem s1_20 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 19)) (R 20) = true := by
  quickRfl

theorem s1_21 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 20)) (R 21) = true := by
  quickRfl

theorem s1_22 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 21)) (R 22) = true := by
  quickRfl

theorem s1_23 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 22)) (R 23) = true := by
  quickRfl

theorem s1_24 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 23)) (R 24) = true := by
  quickRfl

theorem s1_25 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 24)) (R 25) = true := by
  quickRfl

theorem s1_26 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 25)) (R 26) = true := by
  quickRfl

theorem s1_27 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 26)) (R 27) = true := by
  quickRfl

theorem s1_28 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 27)) (R 28) = true := by
  quickRfl

theorem s1_29 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 28)) (R 29) = true := by
  quickRfl

theorem s1_30 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 29)) (R 30) = true := by
  quickRfl

theorem s1_31 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 30)) (R 31) = true := by
  quickRfl

theorem s1_32 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 31)) (R 32) = true := by
  quickRfl

theorem z1 : zS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 1 = R 32 := by
  change closeS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 33 (single 1479) = R 32
  exact closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 32)
    (a := single 1479) (b := R 0) (c := R 32) s1_0
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 31)
    (a := R 0) (b := R 1) (c := R 32) s1_1
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 30)
    (a := R 1) (b := R 2) (c := R 32) s1_2
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 29)
    (a := R 2) (b := R 3) (c := R 32) s1_3
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 28)
    (a := R 3) (b := R 4) (c := R 32) s1_4
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 27)
    (a := R 4) (b := R 5) (c := R 32) s1_5
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 26)
    (a := R 5) (b := R 6) (c := R 32) s1_6
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 25)
    (a := R 6) (b := R 7) (c := R 32) s1_7
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 24)
    (a := R 7) (b := R 8) (c := R 32) s1_8
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 23)
    (a := R 8) (b := R 9) (c := R 32) s1_9
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 22)
    (a := R 9) (b := R 10) (c := R 32) s1_10
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 21)
    (a := R 10) (b := R 11) (c := R 32) s1_11
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 20)
    (a := R 11) (b := R 12) (c := R 32) s1_12
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 19)
    (a := R 12) (b := R 13) (c := R 32) s1_13
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 18)
    (a := R 13) (b := R 14) (c := R 32) s1_14
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 17)
    (a := R 14) (b := R 15) (c := R 32) s1_15
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 16)
    (a := R 15) (b := R 16) (c := R 32) s1_16
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 15)
    (a := R 16) (b := R 17) (c := R 32) s1_17
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 14)
    (a := R 17) (b := R 18) (c := R 32) s1_18
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 13)
    (a := R 18) (b := R 19) (c := R 32) s1_19
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 12)
    (a := R 19) (b := R 20) (c := R 32) s1_20
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 11)
    (a := R 20) (b := R 21) (c := R 32) s1_21
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 10)
    (a := R 21) (b := R 22) (c := R 32) s1_22
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 9)
    (a := R 22) (b := R 23) (c := R 32) s1_23
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 8)
    (a := R 23) (b := R 24) (c := R 32) s1_24
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 7)
    (a := R 24) (b := R 25) (c := R 32) s1_25
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 6)
    (a := R 25) (b := R 26) (c := R 32) s1_26
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 5)
    (a := R 26) (b := R 27) (c := R 32) s1_27
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 4)
    (a := R 27) (b := R 28) (c := R 32) s1_28
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 3)
    (a := R 28) (b := R 29) (c := R 32) s1_29
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 2)
    (a := R 29) (b := R 30) (c := R 32) s1_30
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 1)
    (a := R 30) (b := R 31) (c := R 32) s1_31
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 0)
    (a := R 31) (b := R 32) (c := R 32) s1_32
    (closeS_zero NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 32))))))))))))))))))))))))))))))))))

theorem s2_0 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (single 3)) (R 33) = true := by
  quickRfl

theorem s2_1 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 33)) (R 34) = true := by
  quickRfl

theorem s2_2 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 34)) (R 35) = true := by
  quickRfl

theorem s2_3 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 35)) (R 36) = true := by
  quickRfl

theorem s2_4 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 36)) (R 37) = true := by
  quickRfl

theorem s2_5 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 37)) (R 38) = true := by
  quickRfl

theorem s2_6 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 38)) (R 39) = true := by
  quickRfl

theorem s2_7 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 39)) (R 40) = true := by
  quickRfl

theorem s2_8 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 40)) (R 41) = true := by
  quickRfl

theorem s2_9 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 41)) (R 42) = true := by
  quickRfl

theorem s2_10 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 42)) (R 43) = true := by
  quickRfl

theorem s2_11 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 43)) (R 44) = true := by
  quickRfl

theorem s2_12 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 44)) (R 45) = true := by
  quickRfl

theorem s2_13 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 45)) (R 46) = true := by
  quickRfl

theorem s2_14 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 46)) (R 47) = true := by
  quickRfl

theorem s2_15 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 47)) (R 48) = true := by
  quickRfl

theorem s2_16 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 48)) (R 49) = true := by
  quickRfl

theorem s2_17 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 49)) (R 50) = true := by
  quickRfl

theorem s2_18 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 50)) (R 51) = true := by
  quickRfl

theorem s2_19 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 51)) (R 52) = true := by
  quickRfl

theorem s2_20 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 52)) (R 53) = true := by
  quickRfl

theorem s2_21 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 53)) (R 54) = true := by
  quickRfl

theorem s2_22 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 54)) (R 55) = true := by
  quickRfl

theorem s2_23 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 55)) (R 56) = true := by
  quickRfl

theorem s2_24 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 56)) (R 57) = true := by
  quickRfl

theorem s2_25 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 57)) (R 58) = true := by
  quickRfl

theorem s2_26 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 58)) (R 59) = true := by
  quickRfl

theorem s2_27 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 59)) (R 60) = true := by
  quickRfl

theorem s2_28 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 60)) (R 61) = true := by
  quickRfl

theorem s2_29 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 61)) (R 62) = true := by
  quickRfl

theorem s2_30 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 62)) (R 63) = true := by
  quickRfl

theorem s2_31 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 63)) (R 64) = true := by
  quickRfl

theorem s2_32 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 64)) (R 65) = true := by
  quickRfl

theorem s2_33 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 65)) (R 66) = true := by
  quickRfl

theorem s2_34 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 66)) (R 67) = true := by
  quickRfl

theorem s2_35 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 67)) (R 68) = true := by
  quickRfl

theorem s2_36 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 68)) (R 69) = true := by
  quickRfl

theorem s2_37 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 69)) (R 70) = true := by
  quickRfl

theorem s2_38 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 70)) (R 71) = true := by
  quickRfl

theorem s2_39 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 71)) (R 72) = true := by
  quickRfl

theorem s2_40 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 72)) (R 73) = true := by
  quickRfl

theorem z2 : zS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 2 = R 73 := by
  change closeS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 41 (single 3) = R 73
  exact closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 40)
    (a := single 3) (b := R 33) (c := R 73) s2_0
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 39)
    (a := R 33) (b := R 34) (c := R 73) s2_1
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 38)
    (a := R 34) (b := R 35) (c := R 73) s2_2
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 37)
    (a := R 35) (b := R 36) (c := R 73) s2_3
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 36)
    (a := R 36) (b := R 37) (c := R 73) s2_4
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 35)
    (a := R 37) (b := R 38) (c := R 73) s2_5
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 34)
    (a := R 38) (b := R 39) (c := R 73) s2_6
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 33)
    (a := R 39) (b := R 40) (c := R 73) s2_7
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 32)
    (a := R 40) (b := R 41) (c := R 73) s2_8
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 31)
    (a := R 41) (b := R 42) (c := R 73) s2_9
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 30)
    (a := R 42) (b := R 43) (c := R 73) s2_10
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 29)
    (a := R 43) (b := R 44) (c := R 73) s2_11
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 28)
    (a := R 44) (b := R 45) (c := R 73) s2_12
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 27)
    (a := R 45) (b := R 46) (c := R 73) s2_13
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 26)
    (a := R 46) (b := R 47) (c := R 73) s2_14
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 25)
    (a := R 47) (b := R 48) (c := R 73) s2_15
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 24)
    (a := R 48) (b := R 49) (c := R 73) s2_16
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 23)
    (a := R 49) (b := R 50) (c := R 73) s2_17
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 22)
    (a := R 50) (b := R 51) (c := R 73) s2_18
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 21)
    (a := R 51) (b := R 52) (c := R 73) s2_19
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 20)
    (a := R 52) (b := R 53) (c := R 73) s2_20
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 19)
    (a := R 53) (b := R 54) (c := R 73) s2_21
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 18)
    (a := R 54) (b := R 55) (c := R 73) s2_22
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 17)
    (a := R 55) (b := R 56) (c := R 73) s2_23
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 16)
    (a := R 56) (b := R 57) (c := R 73) s2_24
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 15)
    (a := R 57) (b := R 58) (c := R 73) s2_25
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 14)
    (a := R 58) (b := R 59) (c := R 73) s2_26
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 13)
    (a := R 59) (b := R 60) (c := R 73) s2_27
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 12)
    (a := R 60) (b := R 61) (c := R 73) s2_28
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 11)
    (a := R 61) (b := R 62) (c := R 73) s2_29
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 10)
    (a := R 62) (b := R 63) (c := R 73) s2_30
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 9)
    (a := R 63) (b := R 64) (c := R 73) s2_31
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 8)
    (a := R 64) (b := R 65) (c := R 73) s2_32
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 7)
    (a := R 65) (b := R 66) (c := R 73) s2_33
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 6)
    (a := R 66) (b := R 67) (c := R 73) s2_34
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 5)
    (a := R 67) (b := R 68) (c := R 73) s2_35
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 4)
    (a := R 68) (b := R 69) (c := R 73) s2_36
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 3)
    (a := R 69) (b := R 70) (c := R 73) s2_37
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 2)
    (a := R 70) (b := R 71) (c := R 73) s2_38
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 1)
    (a := R 71) (b := R 72) (c := R 73) s2_39
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 0)
    (a := R 72) (b := R 73) (c := R 73) s2_40
    (closeS_zero NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 73))))))))))))))))))))))))))))))))))))))))))

theorem s3_0 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (single 750020)) (R 74) = true := by
  quickRfl

theorem s3_1 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 74)) (R 75) = true := by
  quickRfl

theorem s3_2 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 75)) (R 76) = true := by
  quickRfl

theorem s3_3 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 76)) (R 77) = true := by
  quickRfl

theorem s3_4 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 77)) (R 78) = true := by
  quickRfl

theorem s3_5 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 78)) (R 79) = true := by
  quickRfl

theorem s3_6 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 79)) (R 80) = true := by
  quickRfl

theorem s3_7 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 80)) (R 81) = true := by
  quickRfl

theorem s3_8 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 81)) (R 82) = true := by
  quickRfl

theorem s3_9 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 82)) (R 83) = true := by
  quickRfl

theorem s3_10 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 83)) (R 84) = true := by
  quickRfl

theorem s3_11 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 84)) (R 85) = true := by
  quickRfl

theorem s3_12 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 85)) (R 86) = true := by
  quickRfl

theorem s3_13 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 86)) (R 87) = true := by
  quickRfl

theorem s3_14 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 87)) (R 88) = true := by
  quickRfl

theorem s3_15 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 88)) (R 89) = true := by
  quickRfl

theorem s3_16 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 89)) (R 90) = true := by
  quickRfl

theorem s3_17 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 90)) (R 91) = true := by
  quickRfl

theorem s3_18 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 91)) (R 92) = true := by
  quickRfl

theorem s3_19 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 92)) (R 93) = true := by
  quickRfl

theorem s3_20 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 93)) (R 94) = true := by
  quickRfl

theorem s3_21 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 94)) (R 95) = true := by
  quickRfl

theorem s3_22 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 95)) (R 96) = true := by
  quickRfl

theorem s3_23 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 96)) (R 97) = true := by
  quickRfl

theorem z3 : zS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 3 = R 97 := by
  change closeS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 24 (single 750020) = R 97
  exact closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 23)
    (a := single 750020) (b := R 74) (c := R 97) s3_0
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 22)
    (a := R 74) (b := R 75) (c := R 97) s3_1
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 21)
    (a := R 75) (b := R 76) (c := R 97) s3_2
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 20)
    (a := R 76) (b := R 77) (c := R 97) s3_3
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 19)
    (a := R 77) (b := R 78) (c := R 97) s3_4
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 18)
    (a := R 78) (b := R 79) (c := R 97) s3_5
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 17)
    (a := R 79) (b := R 80) (c := R 97) s3_6
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 16)
    (a := R 80) (b := R 81) (c := R 97) s3_7
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 15)
    (a := R 81) (b := R 82) (c := R 97) s3_8
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 14)
    (a := R 82) (b := R 83) (c := R 97) s3_9
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 13)
    (a := R 83) (b := R 84) (c := R 97) s3_10
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 12)
    (a := R 84) (b := R 85) (c := R 97) s3_11
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 11)
    (a := R 85) (b := R 86) (c := R 97) s3_12
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 10)
    (a := R 86) (b := R 87) (c := R 97) s3_13
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 9)
    (a := R 87) (b := R 88) (c := R 97) s3_14
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 8)
    (a := R 88) (b := R 89) (c := R 97) s3_15
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 7)
    (a := R 89) (b := R 90) (c := R 97) s3_16
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 6)
    (a := R 90) (b := R 91) (c := R 97) s3_17
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 5)
    (a := R 91) (b := R 92) (c := R 97) s3_18
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 4)
    (a := R 92) (b := R 93) (c := R 97) s3_19
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 3)
    (a := R 93) (b := R 94) (c := R 97) s3_20
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 2)
    (a := R 94) (b := R 95) (c := R 97) s3_21
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 1)
    (a := R 95) (b := R 96) (c := R 97) s3_22
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 0)
    (a := R 96) (b := R 97) (c := R 97) s3_23
    (closeS_zero NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 97)))))))))))))))))))))))))

theorem s4_0 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (single 750100)) (R 98) = true := by
  quickRfl

theorem s4_1 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 98)) (R 99) = true := by
  quickRfl

theorem s4_2 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 99)) (R 100) = true := by
  quickRfl

theorem s4_3 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 100)) (R 101) = true := by
  quickRfl

theorem s4_4 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 101)) (R 102) = true := by
  quickRfl

theorem s4_5 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 102)) (R 103) = true := by
  quickRfl

theorem s4_6 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 103)) (R 104) = true := by
  quickRfl

theorem s4_7 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 104)) (R 105) = true := by
  quickRfl

theorem s4_8 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 105)) (R 106) = true := by
  quickRfl

theorem s4_9 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 106)) (R 107) = true := by
  quickRfl

theorem s4_10 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 107)) (R 108) = true := by
  quickRfl

theorem s4_11 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 108)) (R 109) = true := by
  quickRfl

theorem s4_12 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 109)) (R 110) = true := by
  quickRfl

theorem s4_13 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 110)) (R 111) = true := by
  quickRfl

theorem s4_14 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 111)) (R 112) = true := by
  quickRfl

theorem s4_15 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 112)) (R 113) = true := by
  quickRfl

theorem s4_16 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 113)) (R 114) = true := by
  quickRfl

theorem s4_17 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 114)) (R 115) = true := by
  quickRfl

theorem s4_18 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 115)) (R 116) = true := by
  quickRfl

theorem s4_19 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 116)) (R 117) = true := by
  quickRfl

theorem s4_20 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 117)) (R 118) = true := by
  quickRfl

theorem s4_21 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 118)) (R 119) = true := by
  quickRfl

theorem s4_22 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 119)) (R 120) = true := by
  quickRfl

theorem s4_23 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 120)) (R 121) = true := by
  quickRfl

theorem s4_24 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 121)) (R 122) = true := by
  quickRfl

theorem s4_25 : Nat.beq (roundS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 122)) (R 123) = true := by
  quickRfl

theorem z4 : zS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 4 = R 123 := by
  change closeS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 26 (single 750100) = R 123
  exact closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 25)
    (a := single 750100) (b := R 98) (c := R 123) s4_0
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 24)
    (a := R 98) (b := R 99) (c := R 123) s4_1
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 23)
    (a := R 99) (b := R 100) (c := R 123) s4_2
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 22)
    (a := R 100) (b := R 101) (c := R 123) s4_3
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 21)
    (a := R 101) (b := R 102) (c := R 123) s4_4
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 20)
    (a := R 102) (b := R 103) (c := R 123) s4_5
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 19)
    (a := R 103) (b := R 104) (c := R 123) s4_6
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 18)
    (a := R 104) (b := R 105) (c := R 123) s4_7
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 17)
    (a := R 105) (b := R 106) (c := R 123) s4_8
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 16)
    (a := R 106) (b := R 107) (c := R 123) s4_9
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 15)
    (a := R 107) (b := R 108) (c := R 123) s4_10
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 14)
    (a := R 108) (b := R 109) (c := R 123) s4_11
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 13)
    (a := R 109) (b := R 110) (c := R 123) s4_12
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 12)
    (a := R 110) (b := R 111) (c := R 123) s4_13
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 11)
    (a := R 111) (b := R 112) (c := R 123) s4_14
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 10)
    (a := R 112) (b := R 113) (c := R 123) s4_15
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 9)
    (a := R 113) (b := R 114) (c := R 123) s4_16
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 8)
    (a := R 114) (b := R 115) (c := R 123) s4_17
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 7)
    (a := R 115) (b := R 116) (c := R 123) s4_18
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 6)
    (a := R 116) (b := R 117) (c := R 123) s4_19
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 5)
    (a := R 117) (b := R 118) (c := R 123) s4_20
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 4)
    (a := R 118) (b := R 119) (c := R 123) s4_21
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 3)
    (a := R 119) (b := R 120) (c := R 123) s4_22
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 2)
    (a := R 120) (b := R 121) (c := R 123) s4_23
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 1)
    (a := R 121) (b := R 122) (c := R 123) s4_24
    (closeS_one (NW := NWP) (KA := KAP) (KB := KBP) (gens := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (n := 0)
    (a := R 122) (b := R 123) (c := R 123) s4_25
    (closeS_zero NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (R 123)))))))))))))))))))))))))))

theorem s7_0 : Nat.beq (roundS NWO KAO KBO [-7, -8, -9] (single 99705)) (R 124) = true := by
  quickRfl

theorem s7_1 : Nat.beq (roundS NWO KAO KBO [-7, -8, -9] (R 124)) (R 125) = true := by
  quickRfl

theorem s7_2 : Nat.beq (roundS NWO KAO KBO [-7, -8, -9] (R 125)) (R 126) = true := by
  quickRfl

theorem s7_3 : Nat.beq (roundS NWO KAO KBO [-7, -8, -9] (R 126)) (R 127) = true := by
  quickRfl

theorem s7_4 : Nat.beq (roundS NWO KAO KBO [-7, -8, -9] (R 127)) (R 128) = true := by
  quickRfl

theorem s7_5 : Nat.beq (roundS NWO KAO KBO [-7, -8, -9] (R 128)) (R 129) = true := by
  quickRfl

theorem s7_6 : Nat.beq (roundS NWO KAO KBO [-7, -8, -9] (R 129)) (R 130) = true := by
  quickRfl

theorem s7_7 : Nat.beq (roundS NWO KAO KBO [-7, -8, -9] (R 130)) (R 131) = true := by
  quickRfl

theorem s7_8 : Nat.beq (roundS NWO KAO KBO [-7, -8, -9] (R 131)) (R 132) = true := by
  quickRfl

theorem s7_9 : Nat.beq (roundS NWO KAO KBO [-7, -8, -9] (R 132)) (R 133) = true := by
  quickRfl

theorem zA : closeS NWO KAO KBO [-7, -8, -9] 10 (single 99705) = R 133 :=
  closeS_one (NW := NWO) (KA := KAO) (KB := KBO) (gens := [-7, -8, -9]) (n := 9)
    (a := single 99705) (b := R 124) (c := R 133) s7_0
    (closeS_one (NW := NWO) (KA := KAO) (KB := KBO) (gens := [-7, -8, -9]) (n := 8)
    (a := R 124) (b := R 125) (c := R 133) s7_1
    (closeS_one (NW := NWO) (KA := KAO) (KB := KBO) (gens := [-7, -8, -9]) (n := 7)
    (a := R 125) (b := R 126) (c := R 133) s7_2
    (closeS_one (NW := NWO) (KA := KAO) (KB := KBO) (gens := [-7, -8, -9]) (n := 6)
    (a := R 126) (b := R 127) (c := R 133) s7_3
    (closeS_one (NW := NWO) (KA := KAO) (KB := KBO) (gens := [-7, -8, -9]) (n := 5)
    (a := R 127) (b := R 128) (c := R 133) s7_4
    (closeS_one (NW := NWO) (KA := KAO) (KB := KBO) (gens := [-7, -8, -9]) (n := 4)
    (a := R 128) (b := R 129) (c := R 133) s7_5
    (closeS_one (NW := NWO) (KA := KAO) (KB := KBO) (gens := [-7, -8, -9]) (n := 3)
    (a := R 129) (b := R 130) (c := R 133) s7_6
    (closeS_one (NW := NWO) (KA := KAO) (KB := KBO) (gens := [-7, -8, -9]) (n := 2)
    (a := R 130) (b := R 131) (c := R 133) s7_7
    (closeS_one (NW := NWO) (KA := KAO) (KB := KBO) (gens := [-7, -8, -9]) (n := 1)
    (a := R 131) (b := R 132) (c := R 133) s7_8
    (closeS_one (NW := NWO) (KA := KAO) (KB := KBO) (gens := [-7, -8, -9]) (n := 0)
    (a := R 132) (b := R 133) (c := R 133) s7_9
    (closeS_zero NWO KAO KBO [-7, -8, -9] (R 133)))))))))))

theorem z0 : zS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 0 = single 0 := by
  change closeS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 0 (single 0) = single 0
  exact closeS_zero NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (single 0)

theorem z5 : zS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 5 = single 1 := by
  change closeS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 0 (single 1) = single 1
  exact closeS_zero NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (single 1)

theorem z6 : zS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 6 = single 2 := by
  change closeS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] 0 (single 2) = single 2
  exact closeS_zero NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (single 2)

@[expose] noncomputable def gS7 : Nat → Nat := sel7 (single 0) (R 32) (R 73) (R 97) (R 123) (single 1) (single 2)

theorem c0 : closedS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (gS7 0) = true := by quickRfl

theorem m0 : cntOK (Nat.land (gS7 0) ptsS) (gSize 0) = true := by quickRfl

theorem d0 : distSetOK NWP KAP KBP gS7 0 = true := by quickRfl

theorem c1 : closedS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (gS7 1) = true := by quickRfl

theorem m1 : cntOK (Nat.land (gS7 1) ptsS) (gSize 1) = true := by quickRfl

theorem d1 : distSetOK NWP KAP KBP gS7 1 = true := by quickRfl

theorem c2 : closedS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (gS7 2) = true := by quickRfl

theorem m2 : cntOK (Nat.land (gS7 2) ptsS) (gSize 2) = true := by quickRfl

theorem d2 : distSetOK NWP KAP KBP gS7 2 = true := by quickRfl

theorem c3 : closedS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (gS7 3) = true := by quickRfl

theorem m3 : cntOK (Nat.land (gS7 3) ptsS) (gSize 3) = true := by quickRfl

theorem d3 : distSetOK NWP KAP KBP gS7 3 = true := by quickRfl

theorem c4 : closedS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (gS7 4) = true := by quickRfl

theorem m4 : cntOK (Nat.land (gS7 4) ptsS) (gSize 4) = true := by quickRfl

theorem d4 : distSetOK NWP KAP KBP gS7 4 = true := by quickRfl

theorem c5 : closedS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (gS7 5) = true := by quickRfl

theorem m5 : cntOK (Nat.land (gS7 5) ptsS) (gSize 5) = true := by quickRfl

theorem d5 : distSetOK NWP KAP KBP gS7 5 = true := by quickRfl

theorem c6 : closedS NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] (gS7 6) = true := by quickRfl

theorem m6 : cntOK (Nat.land (gS7 6) ptsS) (gSize 6) = true := by quickRfl

theorem d6 : distSetOK NWP KAP KBP gS7 6 = true := by quickRfl

theorem dc : andB (allI 7 fun i => allI 7 fun j => orB (Nat.beq i j)
    (Nat.beq (Nat.land (gS7 i) (gS7 j)) 0)) (Nat.beq (Nat.land (lorI gS7 7) ptsS) ptsS) = true := by
  quickRfl

theorem cA : closedS NWO KAO KBO [-7, -8, -9] (R 133) = true := by quickRfl

theorem mA : cntOK (Nat.land (R 133) ptsS) 3510 = true := by quickRfl

theorem rA : andB (allI 3 fun t => andB (ptOK NWO KAO KBO [((t + 7 : Nat) : Int)] 0 0)
    (ptOK NWO KAO KBO [((t + 7 : Nat) : Int)] 1479 1479))
    (letB (Nat.land (imgS NWO KAO KBO (-10) (gS7 1)) (gS7 1)) fun X => Nat.beq (Nat.land X (R 133)) X) =
    true := by
  quickRfl

end CFSG.KD.RouteP.GeomLv

namespace CFSG.KD.RouteP.GeomCk

open CFSG.KC.RouteP CFSG.KD.RouteP.GeomLv

theorem geomSet : geomSetOK NWP KAP KBP NWO KAO KBO [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]
    [-7, -8, -9] = true :=
  geomSetOK_of (S := gS7) z0 z1 z2 z3 z4 z5 z6 zA rfl (lt7 c0 c1 c2 c3 c4 c5 c6)
    (lt7 m0 m1 m2 m3 m4 m5 m6) dc (lt7 d0 d1 d2 d3 d4 d5 d6) cA mA rA

end CFSG.KD.RouteP.GeomCk

end
