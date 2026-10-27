module

public import Certificates.Kernel.Fi23S.ChkDefs
public import Certificates.Kernel.Fi23Sq.Codes

public section

namespace CFSG.KD.Fi23Sq

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23S CFSG.KS.PEnum CFSG.KD.Fi23K
  CFSG.KD.Fi23S

@[expose] def D0L : List Nat := [11396, 7615, 2, 4491, 27086, 29513]

@[expose] noncomputable def d0 (q : Nat) : Nat := List.getD D0L q (nat_lit 0)

@[expose] noncomputable def d0Ok (L : List Nat) : Bool :=
  allN (nat_lit 6) fun q => Nat.beq (tA G (nat_lit 2776) q) (List.getD L q (nat_lit 0))

@[expose] noncomputable def wz (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun z _ ih => tb G (Nat.add (nat_lit 52) z) ih) w

@[expose] noncomputable def wzi (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => strictN (tb G (Nat.add (nat_lit 52) (Nat.xor z (nat_lit 1))) x) ih) w x

@[expose] noncomputable def rhoW (a b : Nat) (w : List Nat) (y : Nat) : Nat :=
  wz w (gK a b (wzi w y))

@[expose] noncomputable def rW (a b : Nat) (w : List Nat) (y : Nat) : Nat :=
  wz w (gK a b (gK a b (wzi w y)))

@[expose] noncomputable def famE (a b : Nat) (w : List Nat) : Bool :=
  bAnd(Nat.blt a (nat_lit 512), bAnd(Nat.blt b (nat_lit 512),
  bAnd(List.rec (motive := fun _ => Bool) true (fun z _ ih => bAnd(Nat.blt z (nat_lit 24), ih)) w,
  bAnd(Nat.beq (rhoW a b w (nat_lit 2776)) (nat_lit 2776),
    fixB fun x => rW a b w (rW a b w x)))))

@[expose] def FA : List Nat := [399, 461, 410, 299, 432, 298, 500, 359, 61, 132, 212, 67, 31, 364,
  359, 314, 4, 394, 252, 225, 501, 269, 235, 213, 190, 176, 77, 135, 22, 450, 317, 36, 238, 207, 272]

@[expose] def FB : List Nat := [397, 85, 60, 476, 334, 327, 477, 217, 26, 177, 306, 216, 56, 95, 102,
  210, 469, 71, 299, 504, 236, 396, 325, 65, 140, 105, 466, 416, 150, 482, 269, 308, 451, 345, 39]

@[expose] def FW : List (List Nat) := [[8, 8, 8, 2, 10, 21, 2, 4], [8, 8, 8, 2, 2, 1, 3, 13, 11, 16],
  [8, 8, 8, 2, 7, 14, 2, 13], [8, 8, 8, 2, 11, 15, 7], [8, 8, 8, 2, 2, 2, 1, 11, 8],
  [8, 8, 8, 2, 16, 7, 14], [8, 8, 8, 2, 16, 7, 14], [8, 8, 8, 2, 11, 2, 8, 10],
  [8, 8, 8, 2, 2, 1, 3, 1, 13, 14, 8], [8, 8, 8, 2, 18, 3, 12, 4], [8, 8, 8, 2, 2, 1, 3, 3, 14, 19],
  [8, 8, 8, 2, 2, 1, 4, 1, 6, 18], [8, 8, 8, 2, 2, 2, 16, 18, 2, 4], [8, 8, 8, 2, 4, 2, 12, 18],
  [8, 8, 8, 2, 2, 1, 3, 7, 4, 10], [8, 8, 8, 2, 2, 1, 2, 12, 5], [8, 8, 8, 2, 2, 1, 2, 4, 19, 21],
  [8, 8, 8, 2, 1, 18, 3, 23], [8, 8, 8, 2, 5, 6, 15, 3], [8, 8, 8, 17, 5, 11],
  [8, 8, 8, 2, 10, 2, 17, 23], [8, 8, 8, 2, 6, 14, 21], [8, 8, 8, 2, 2, 1, 6, 14, 3, 14],
  [8, 8, 8, 2, 8, 7, 4], [8, 8, 8, 2, 2, 2, 10, 17, 12], [8, 8, 8, 2, 4, 7, 2, 7],
  [8, 8, 8, 2, 1, 16, 16], [8, 8, 8, 2, 11, 2, 6], [8, 8, 8, 2, 2, 2, 1, 2, 7],
  [8, 8, 8, 2, 2, 1, 5, 21], [8, 8, 8, 2, 8, 7, 4], [8, 8, 8, 2, 2, 1, 6, 21, 3, 5],
  [8, 8, 8, 2, 16, 3, 3], [8, 8, 8, 2, 10, 13, 3, 18], [8, 8, 8, 2, 21, 2, 8, 19]]

@[expose] noncomputable def famF (f : Nat) : Bool :=
  famE (List.getD FA f (nat_lit 0)) (List.getD FB f (nat_lit 0)) (List.getD FW f [])

@[expose] noncomputable def rF (f y : Nat) : Nat :=
  rW (List.getD FA f (nat_lit 0)) (List.getD FB f (nat_lit 0)) (List.getD FW f []) y

@[expose] noncomputable def miscSq : Bool :=
  bAnd(d0Ok D0L, bAnd(allN (nat_lit 42) fun l => Nat.beq (tb H l (nat_lit 2776)) (nat_lit 2776),
    allN (nat_lit 35) famF))

@[expose] noncomputable def cq (i : Nat) : Nat := r32 CQ i

@[expose] noncomputable def cA (k j : Nat) : Nat :=
  cq (Nat.mul (nat_lit 2) (Nat.add (Nat.mul k (nat_lit 512)) j))

@[expose] noncomputable def cB (k j : Nat) : Nat :=
  cq (Nat.succ (Nat.mul (nat_lit 2) (Nat.add (Nat.mul k (nat_lit 512)) j)))

@[expose] noncomputable def gP (p x : Nat) : Nat :=
  gK (Nat.shiftRight p (nat_lit 9)) (Nat.land p (nat_lit 511)) x

@[expose] noncomputable def hF (k j f y : Nat) : Nat := gK k j (rF f y)

@[expose] noncomputable def lfT (t p u k j : Nat) : Bool :=
  bIf(Nat.beq t (nat_lit 0), Nat.blt (code k j) (nat_lit 2),
  bIf(Nat.beq t (nat_lit 1), Nat.ble (nat_lit 110) (code k j),
  bIf(Nat.beq t (nat_lit 2),
    bAnd(Nat.blt p (nat_lit 262144), bAnd(Nat.ble (nat_lit 110)
      (code (Nat.shiftRight p (nat_lit 9)) (Nat.land p (nat_lit 511))),
      allN (nat_lit 6) fun b => Nat.beq (gP p (gK k j b)) (d0 b))),
  bIf(Nat.beq t (nat_lit 3),
    bAnd(Nat.blt p (nat_lit 35), allN (nat_lit 6) fun q =>
      strictB (cyK (hF k j p) q (nat_lit 119) (nat_lit 1) (hF k j p q)) fun l =>
        Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 1)),
  bIf(Nat.beq t (nat_lit 4),
    bAnd(Nat.blt p (nat_lit 262144), bAnd(Nat.blt u (nat_lit 262144),
    bAnd(Nat.beq (Nat.land (Nat.shiftRight
      (cA (Nat.shiftRight p (nat_lit 9)) (Nat.land p (nat_lit 511))) (nat_lit 3)) (nat_lit 7))
      (nat_lit 3),
      allN (nat_lit 6) fun b => Nat.beq (gK k j (gP u b)) (gP u (gP p b))))),
    false)))))

@[expose] noncomputable def lfC (c u k j : Nat) : Bool :=
  strictB (Nat.land c (nat_lit 7)) fun q =>
    bAnd(Nat.blt q (nat_lit 6), bAnd(Bool.not (Nat.beq (gK k j (gK k j q)) (d0 q)),
      lfT (Nat.land (Nat.shiftRight c (nat_lit 3)) (nat_lit 7)) (Nat.shiftRight c (nat_lit 6)) u k j))

@[expose] noncomputable def lfSq (k j : Nat) : Bool :=
  strictB (cA k j) fun c => lfC c (cB k j) k j

@[expose] noncomputable def lSqSl (k0 nk : Nat) : Bool :=
  allN nk fun d => strictB (Nat.add k0 d) fun k => allN (nat_lit 512) (lfSq k)

@[expose] def lSqB : List Nat :=
  [0, 38, 72, 107, 141, 175, 210, 241, 272, 302, 332, 362, 392, 422, 453, 483, 512]

@[expose] noncomputable def lSqF (s : Nat) : Bool :=
  strictB (List.getD lSqB s (nat_lit 0)) fun a =>
    lSqSl a (Nat.sub (List.getD lSqB (Nat.succ s) (nat_lit 0)) a)

end CFSG.KD.Fi23Sq

end
