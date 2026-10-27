module

public import Certificates.Kernel.Om1K.Enum
public import Certificates.Kernel.Om1K.Elts
public import Certificates.Kernel.Om1K.BData

public section

namespace CertificateChecks.KernelOm1.B

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim
open CertificateChecks.KernelOm2 (pc2 wAK)
open CertificateChecks.KernelLC.E8 (FT NEG)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data (wDT)

@[expose] noncomputable def ip (p i : Nat) : Nat := pg 8 255 p i

@[expose] noncomputable def pc (p q : Nat) : Nat := pc2 p q

@[expose] noncomputable def pid : Nat := pidn 240 8

@[expose] noncomputable def cnK (p : Nat) : Bool := canonK 240 8 (mask 8) (240 * 8) p

@[expose] noncomputable def neAt (a b p : Nat) : Bool :=
  bAnd(Nat.blt p 240, bIf(Nat.beq (ip a p) (ip b p), false, true))

@[expose] noncomputable def gI (G : Nat → Nat) (ng k : Nat) : Nat := nIf(Nat.beq k ng, pid, G k)

@[expose] noncomputable def q8K (x y : Nat) : List Nat :=
  [pid, x, pc x x, pc (pc x x) x, y, pc y x, pc y (pc x x), pc y (pc (pc x x) x)]

@[expose] noncomputable def T0 : Nat := FT 15

@[expose] noncomputable def TA : Nat := FT 3

@[expose] noncomputable def TB : Nat := FT 252

@[expose] noncomputable def TC : Nat := FT 23

@[expose] noncomputable def krOK (k : Nat) : Bool :=
  Nat.beq (BD.KR k) ((q8K (A.EL.G 1) (A.EL.G 2)).getD k 0)

@[expose] noncomputable def ksOK (KS : Nat → Nat) (k : Nat) : Bool :=
  bAnd(cnK (KS k), Nat.beq (pc (A.EL.G 3) (BD.KR k)) (pc (KS k) (A.EL.G 3)))

@[expose] noncomputable def lhOK (G A AI R : Nat → Nat) (ng h : Nat) : Bool :=
  strictB (R h) (fun r => strictB fld(r, 0, 15) (fun a => strictB fld(r, 4, 15) (fun b =>
    bAnd(Nat.ble a ng, bAnd(Nat.ble b ng,
    bAnd(Nat.beq (A h) (pc (gI G ng a) (gI G ng b)),
    bAnd(Nat.beq (pc (A h) (AI h)) pid, cnK (AI h))))))))

@[expose] noncomputable def dtOK (DG DF : Nat → Nat) (j : Nat) : Bool :=
  strictB (wAK (wDT.getD j [])) (fun g => strictB (DF j) (fun f =>
    bAnd(cnK (DG j), bAnd(Nat.beq (pc (DG j) g) (pc g T0),
    bAnd(neAt (DG j) T0 fld(f, 0, 255), neAt (DG j) (pc T0 NEG) fld(f, 8, 255))))))

@[expose] noncomputable def wLet (x xv l : Nat) : Nat :=
  strictN fld(l, 0, 3) (fun ty => strictN fld(l, 2, 127) (fun k =>
    nIf(Nat.beq ty 0, EK.T k, nIf(Nat.beq ty 3, x,
      pc (BD.LhG k) (pc (nIf(Nat.beq ty 1, x, xv)) (BD.LhI k))))))

@[expose] noncomputable def wLetOK (l : Nat) : Bool :=
  strictB fld(l, 0, 3) (fun ty => strictB fld(l, 2, 127) (fun k =>
    bIf(Nat.beq ty 0, Nat.blt k 32, bIf(Nat.beq ty 3, true, Nat.blt k 57))))

@[expose] noncomputable def wInv (l : Nat) : Bool := Nat.beq fld(l, 0, 3) 2

@[expose] noncomputable def wProd (x xv nl l1 l2 l3 l4 : Nat) : Nat :=
  nIf(Nat.beq nl 1, wLet x xv l1, nIf(Nat.beq nl 2, pc (wLet x xv l1) (wLet x xv l2),
    nIf(Nat.beq nl 3, pc (wLet x xv l1) (pc (wLet x xv l2) (wLet x xv l3)),
      pc (wLet x xv l1) (pc (wLet x xv l2) (pc (wLet x xv l3) (wLet x xv l4))))))

@[expose] noncomputable def witOK (E : Nat → Nat) (nE : Nat) (W : Nat → Nat) (i : Nat) : Bool :=
  strictB (W i) (fun r => strictB fld(r, 0, 7) (fun nl =>
    bIf(Nat.beq nl 0, true,
    strictB fld(r, 3, 511) (fun l1 => strictB fld(r, 12, 511) (fun l2 =>
    strictB fld(r, 21, 511) (fun l3 => strictB fld(r, 30, 511) (fun l4 =>
    strictB fld(r, 39, 8191) (fun xi => strictB fld(r, 52, 255) (fun j =>
    strictB (E i) (fun x => strictB (E xi) (fun xv =>
    bAnd(Nat.ble nl 4, bAnd(Nat.blt xi nE, bAnd(Nat.blt j 204,
    bAnd(wLetOK l1, bAnd(wLetOK l2, bAnd(wLetOK l3, bAnd(wLetOK l4,
    bAnd(bIf(wInv l1 || wInv l2 || wInv l3 || wInv l4, Nat.beq (pc x xv) pid, true),
      Nat.beq (wProd x xv nl l1 l2 l3 l4) (BD.DG j))))))))))))))))))))

@[expose] noncomputable def noWit (W : Nat → Nat) (i : Nat) : Bool := Nat.beq fld(W i, 0, 7) 0

@[expose] noncomputable def cntN (n : Nat) (p : Nat → Bool) : Nat :=
  foldN n (fun i s => nIf(p i, Nat.succ s, s)) 0

@[expose] noncomputable def xpw (x k q : Nat) : Nat :=
  nIf(Nat.beq k 0, q, nIf(Nat.beq k 1, ip x q, nIf(Nat.beq k 2, ip x (ip x q), ip x (ip x (ip x q)))))

@[expose] noncomputable def cjAt (s si g q : Nat) : Nat := ip s (ip g (ip si q))

@[expose] noncomputable def sqOK (E SQ RT : Nat → Nat) (tt nR i : Nat) : Bool :=
  strictB (SQ i) (fun r => strictB (E i) (fun x =>
    bIf(Nat.beq fld(r, 0, 1) 1, strictB fld(r, 1, 255) (fun a =>
      bAnd(Nat.blt a nR, Nat.beq fld(RT a, 0, 8191) i)),
    strictB fld(r, 1, 255) (fun p => bAnd(Nat.blt p 240,
      bIf(Nat.beq (ip x (ip x p)) (ip tt p), false, true))))))

@[expose] noncomputable def rootOK (E RT : Nat → Nat) (nE a : Nat) : Bool :=
  strictB (RT a) (fun r => bAnd(Nat.blt fld(r, 0, 8191) nE,
    bAnd(bIf(Nat.beq fld(r, 13, 1) 1, Nat.beq (E fld(r, 0, 8191)) (BD.KR fld(r, 14, 7)), true),
      bIf(Nat.beq fld(r, 17, 1) 1, Nat.beq (E fld(r, 0, 8191)) (BD.KS fld(r, 18, 7)), true))))

@[expose] noncomputable def twinOK (x y s si r : Nat) : Bool :=
  strictB (nIf(Nat.beq fld(r, 17, 1) 0, x, y)) (fun g =>
  strictB (nIf(Nat.beq fld(r, 18, 1) 0, x, y)) (fun a =>
  strictB (nIf(Nat.beq fld(r, 19, 1) 0, x, y)) (fun b =>
  strictB fld(r, 2, 255) (fun p =>
    bAnd(allN 4 (fun k => strictB fld(r, Nat.add 20 (Nat.mul 8 k), 255) (fun q =>
      bAnd(Nat.blt q 240, bIf(Nat.beq (cjAt s si g q) (xpw x k q), false, true)))),
    bAnd(allN 4 (fun k => strictB fld(r, Nat.add 52 (Nat.mul 8 k), 255) (fun q =>
      bAnd(Nat.blt q 240, bIf(Nat.beq (cjAt s si g q) (ip y (xpw x k q)), false, true)))),
    bAnd(Nat.blt p 240,
      bIf(Nat.beq (ip a (cjAt s si b p)) (cjAt s si b (ip a p)), false, true))))))))

@[expose] noncomputable def q8Pair (E RT Lg LgI : Nat → Nat) (nL : Nat) (withR : Bool)
    (a x row b : Nat) : Bool :=
  strictB fld(row, Nat.mul 96 b, 19342813113834066795298815) (fun r =>
  strictB (E fld(RT b, 0, 8191)) (fun y =>
  strictB fld(r, 0, 3) (fun kd => strictB fld(r, 2, 255) (fun p =>
    bIf(Nat.beq kd 0, bAnd(Nat.blt p 240,
        bIf(Nat.beq (ip y (ip x p)) (ip x (ip x (ip x (ip y p)))), false, true)),
    bIf(Nat.beq kd 1, bAnd(withR, bAnd(Nat.beq fld(RT a, 13, 1) 1, Nat.beq fld(RT b, 13, 1) 1)),
    bIf(Nat.beq kd 3, bAnd(withR, bAnd(Nat.beq fld(RT a, 17, 1) 1, Nat.beq fld(RT b, 17, 1) 1)),
      strictB fld(r, 10, 127) (fun h => bAnd(Nat.blt h nL, twinOK x y (Lg h) (LgI h) r)))))))))

@[expose] noncomputable def q8Row (E RT PR Lg LgI : Nat → Nat) (nL nR : Nat) (withR : Bool)
    (a : Nat) : Bool :=
  strictB (PR a) (fun row => strictB (E fld(RT a, 0, 8191)) (fun x =>
    allN nR (q8Pair E RT Lg LgI nL withR a x row)))

@[expose] noncomputable def oc (c m : Nat) : Nat :=
  nIf(Nat.beq c 0, BD.OA m, nIf(Nat.beq c 1, BD.OB m, nIf(Nat.beq c 2, BD.OC m, BD.OD m)))

@[expose] noncomputable def oNodeOK (OP : Nat → Nat) (m : Nat) : Bool :=
  strictB (OP m) (fun r => strictB fld(r, 0, 1023) (fun par => strictB fld(r, 10, 7) (fun k =>
    bAnd(allN 4 (fun c => cnK (oc c m)),
    bIf(Nat.beq m 0,
      bAnd(Nat.beq (BD.OA 0) (A.EL.G 1), bAnd(Nat.beq (BD.OB 0) (A.EL.G 2),
      bAnd(Nat.beq (pc (A.EL.G 3) (A.EL.G 1)) (pc (BD.OC 0) (A.EL.G 3)),
        Nat.beq (pc (A.EL.G 3) (A.EL.G 2)) (pc (BD.OD 0) (A.EL.G 3))))),
      bAnd(Nat.blt par m, bAnd(Nat.blt k 7,
        allN 4 (fun c => Nat.beq (pc (A.TG.G k) (oc c par)) (pc (oc c m) (A.TG.G k))))))))))

@[expose] noncomputable def tupK (m : Nat) : Nat :=
  Nat.add (BD.OA m) (Nat.shiftLeft (Nat.add (BD.OB m) (Nat.shiftLeft (Nat.add (BD.OC m)
    (Nat.shiftLeft (BD.OD m) 1920)) 1920)) 1920)

@[expose] noncomputable def wit0c (c : Nat) : Bool :=
  allN 64 (fun d => witOK E0.T 4096 BD.W0 (Nat.add (Nat.mul 64 c) d))

@[expose] noncomputable def q80c (c : Nat) : Bool :=
  allN 16 (fun d => q8Row E0.T BD.RT0 BD.PR0 BD.LhG BD.LhI 57 240 true (Nat.add (Nat.mul 16 c) d))

@[expose] noncomputable def q8ac (c : Nat) : Bool :=
  allN 16 (fun d => q8Row Ea.T BD.RTa BD.PRa BD.LhG BD.LhI 0 96 false (Nat.add (Nat.mul 16 c) d))

@[expose] noncomputable def q8cc (c : Nat) : Bool :=
  allN 16 (fun d => q8Row Ec.T BD.RTc BD.PRc BD.LcG BD.LcI 31 48 false (Nat.add (Nat.mul 16 c) d))

end CertificateChecks.KernelOm1.B

end
