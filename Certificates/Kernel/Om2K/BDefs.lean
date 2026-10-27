module

public import Certificates.Kernel.Om2K.Enum
public import Certificates.Kernel.Om2K.BData

public section

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def ip (p i : Nat) : Nat := pg 9 511 p i

@[expose] noncomputable def cnK (p : Nat) : Bool := canonK 480 9 (mask 9) (480 * 9) p

@[expose] noncomputable def neAt (a b p : Nat) : Bool :=
  bAnd(Nat.blt p 480, bIf(Nat.beq (ip a p) (ip b p), false, true))

@[expose] noncomputable def gI (G : Nat → Nat) (ng k : Nat) : Nat := nIf(Nat.beq k ng, pid, G k)

@[expose] noncomputable def lhOK (G A AI R : Nat → Nat) (ng h : Nat) : Bool :=
  strictB (R h) (fun r => strictB fld(r, 0, 15) (fun a => strictB fld(r, 4, 15) (fun b =>
    bAnd(Nat.ble a ng, bAnd(Nat.ble b ng,
    bAnd(Nat.beq (A h) (pc (gI G ng a) (gI G ng b)),
    bAnd(Nat.beq (pc (A h) (AI h)) pid, cnK (AI h))))))))

@[expose] noncomputable def zOK (k : Nat) : Bool :=
  bIf(Nat.beq k 0, Nat.beq (BD.ZT 0) (EL.G 0), Nat.beq (BD.ZT k) (pc (EL.G 0) (cAK (Nat.sub k 1))))

@[expose] noncomputable def kgOK (k : Nat) : Bool := Nat.beq (BD.KG k) ((q8K (EL.G 1) (EL.G 2)).getD k 0)

@[expose] noncomputable def flagOK (d f : Nat) : Bool :=
  bAnd(bIf(Nat.beq fld(f, 0, 1) 1, neAt d (BD.ZT 0) fld(f, 1, 511), true),
    bIf(Nat.beq fld(f, 10, 1) 1, bAnd(Nat.beq fld(f, 0, 1) 1,
      bAnd(neAt d (BD.ZT 1) fld(f, 11, 511), bAnd(neAt d (BD.ZT 2) fld(f, 20, 511),
        neAt d (BD.ZT 3) fld(f, 29, 511)))), true))

@[expose] noncomputable def nodeOK (NG NP NF : Nat → Nat) (j : Nat) : Bool :=
  strictB (NP j) (fun r => strictB fld(r, 0, 4095) (fun par => strictB fld(r, 12, 15) (fun l =>
    bAnd(cnK (NG j), bAnd(flagOK (NG j) (NF j),
      bIf(Nat.beq j 0, Nat.beq (NG 0) (EL.G 0),
        bAnd(Nat.blt par j, Nat.beq (pc (L.G l) (NG par)) (pc (NG j) (L.G l)))))))))

@[expose] noncomputable def wLet (x xv l : Nat) : Nat :=
  strictN fld(l, 0, 3) (fun ty => strictN fld(l, 2, 127) (fun k =>
    nIf(Nat.beq ty 0, BD.KG k, nIf(Nat.beq ty 3, x,
      pc (BD.LhG k) (pc (nIf(Nat.beq ty 1, x, xv)) (BD.LhI k))))))

@[expose] noncomputable def wLetOK (l : Nat) : Bool :=
  strictB fld(l, 0, 3) (fun ty => strictB fld(l, 2, 127) (fun k =>
    bIf(Nat.beq ty 0, Nat.blt k 8, bIf(Nat.beq ty 3, true, Nat.blt k 73))))

@[expose] noncomputable def wInv (l : Nat) : Bool := Nat.beq fld(l, 0, 3) 2

@[expose] noncomputable def wProd (x xv nl l1 l2 l3 : Nat) : Nat :=
  nIf(Nat.beq nl 1, wLet x xv l1, nIf(Nat.beq nl 2, pc (wLet x xv l1) (wLet x xv l2),
    pc (wLet x xv l1) (pc (wLet x xv l2) (wLet x xv l3))))

@[expose] noncomputable def witOK (E : Nat → Nat) (nE : Nat) (W : Nat → Nat) (i : Nat) : Bool :=
  strictB (W i) (fun r => strictB fld(r, 0, 3) (fun nl =>
    bIf(Nat.beq nl 0, true,
    strictB fld(r, 2, 511) (fun l1 => strictB fld(r, 11, 511) (fun l2 =>
    strictB fld(r, 20, 511) (fun l3 => strictB fld(r, 29, 8191) (fun xi =>
    strictB fld(r, 42, 4095) (fun j => strictB (E i) (fun x => strictB (E xi) (fun xv =>
    bAnd(Nat.blt nl 4, bAnd(Nat.blt xi nE, bAnd(Nat.blt j BD.nN,
    bAnd(Nat.beq fld(BD.NF j, 0, 1) 1, bAnd(wLetOK l1, bAnd(wLetOK l2, bAnd(wLetOK l3,
    bAnd(bIf(wInv l1 || wInv l2 || wInv l3, Nat.beq (pc x xv) pid, true),
      Nat.beq (wProd x xv nl l1 l2 l3) (BD.NG j)))))))))))))))))))

@[expose] noncomputable def noWit (W : Nat → Nat) (f i : Nat) : Bool :=
  strictB (W i) (fun r =>
    bIf(Nat.beq fld(r, 0, 3) 0, true, Nat.beq fld(BD.NF fld(r, 42, 4095), f, 1) 0))

@[expose] noncomputable def cntN (n : Nat) (p : Nat → Bool) : Nat :=
  foldN n (fun i s => nIf(p i, Nat.succ s, s)) 0

@[expose] noncomputable def xpw (x k q : Nat) : Nat :=
  nIf(Nat.beq k 0, q, nIf(Nat.beq k 1, ip x q, nIf(Nat.beq k 2, ip x (ip x q), ip x (ip x (ip x q)))))

@[expose] noncomputable def cjAt (s si g q : Nat) : Nat := ip s (ip g (ip si q))

@[expose] noncomputable def sqOK (E SQ RT : Nat → Nat) (tt nR i : Nat) : Bool :=
  strictB (SQ i) (fun r => strictB (E i) (fun x =>
    bIf(Nat.beq fld(r, 0, 1) 1, strictB fld(r, 1, 255) (fun a =>
      bAnd(Nat.blt a nR, Nat.beq fld(RT a, 0, 8191) i)),
    strictB fld(r, 1, 511) (fun p => bAnd(Nat.blt p 480,
      bIf(Nat.beq (ip x (ip x p)) (ip tt p), false, true))))))

@[expose] noncomputable def rootOK (E RT : Nat → Nat) (nE a : Nat) : Bool :=
  strictB (RT a) (fun r => bAnd(Nat.blt fld(r, 0, 8191) nE,
    bIf(Nat.beq fld(r, 13, 1) 1, Nat.beq (E fld(r, 0, 8191)) (BD.KG fld(r, 14, 7)), true)))

@[expose] noncomputable def twinOK (x y s si r : Nat) : Bool :=
  strictB (nIf(Nat.beq fld(r, 18, 1) 0, x, y)) (fun g =>
  strictB (nIf(Nat.beq fld(r, 19, 1) 0, x, y)) (fun a =>
  strictB (nIf(Nat.beq fld(r, 20, 1) 0, x, y)) (fun b =>
  strictB fld(r, 2, 511) (fun p =>
    bAnd(allN 4 (fun k => strictB fld(r, Nat.add 21 (Nat.mul 9 k), 511) (fun q =>
      bAnd(Nat.blt q 480, bIf(Nat.beq (cjAt s si g q) (xpw x k q), false, true)))),
    bAnd(allN 4 (fun k => strictB fld(r, Nat.add 57 (Nat.mul 9 k), 511) (fun q =>
      bAnd(Nat.blt q 480, bIf(Nat.beq (cjAt s si g q) (ip y (xpw x k q)), false, true)))),
    bAnd(Nat.blt p 480,
      bIf(Nat.beq (ip a (cjAt s si b p)) (cjAt s si b (ip a p)), false, true))))))))

@[expose] noncomputable def q8Pair (E RT Lg LgI : Nat → Nat) (nL : Nat) (withR : Bool)
    (a x row b : Nat) : Bool :=
  strictB fld(row, Nat.mul 96 b, 9903520314283042199192993791) (fun r =>
  strictB (E fld(RT b, 0, 8191)) (fun y =>
  strictB fld(r, 0, 3) (fun kd => strictB fld(r, 2, 511) (fun p =>
    bIf(Nat.beq kd 0, bAnd(Nat.blt p 480,
        bIf(Nat.beq (ip y (ip x p)) (ip x (ip x (ip x (ip y p)))), false, true)),
    bIf(Nat.beq kd 1, bAnd(withR, bAnd(Nat.beq fld(RT a, 13, 1) 1, Nat.beq fld(RT b, 13, 1) 1)),
      bAnd(Nat.beq kd 2, strictB fld(r, 11, 127) (fun h =>
        bAnd(Nat.blt h nL, twinOK x y (Lg h) (LgI h) r)))))))))

@[expose] noncomputable def q8Row (E RT PR Lg LgI : Nat → Nat) (nL nR : Nat) (withR : Bool)
    (a : Nat) : Bool :=
  strictB (PR a) (fun row => strictB (E fld(RT a, 0, 8191)) (fun x =>
    allN nR (q8Pair E RT Lg LgI nL withR a x row)))

@[expose] noncomputable def oNodeOK (m : Nat) : Bool :=
  strictB (BD.OP m) (fun r => strictB fld(r, 0, 31) (fun par => strictB fld(r, 5, 15) (fun k =>
    bAnd(cnK (BD.OA m), bAnd(cnK (BD.OB m),
    bIf(Nat.beq m 0, bAnd(Nat.beq (BD.OA 0) (EL.G 1), Nat.beq (BD.OB 0) (EL.G 2)),
      bAnd(Nat.blt par m, bAnd(Nat.blt k 8,
      bAnd(Nat.beq (pc (TG.G k) (BD.OA par)) (pc (BD.OA m) (TG.G k)),
        Nat.beq (pc (TG.G k) (BD.OB par)) (pc (BD.OB m) (TG.G k)))))))))))

@[expose] noncomputable def oDistOK (m : Nat) : Bool :=
  allN 24 (fun m' => bIf(Nat.blt m m', strictB (BD.OD (Nat.add (Nat.mul 24 m) m')) (fun r =>
    bIf(Nat.beq fld(r, 0, 1) 0, neAt (BD.OA m) (BD.OA m') fld(r, 1, 511),
      neAt (BD.OB m) (BD.OB m') fld(r, 1, 511))), true))

@[expose] noncomputable def sgOK (m : Nat) : Bool :=
  strictB (Nat.div m 2) (fun f => strictB (EL.G (Nat.add 1 (Nat.mod m 2))) (fun X =>
    bAnd(cnK (BD.SG m), bIf(Nat.beq f 0, Nat.beq (BD.SG m) X,
      bAnd(Nat.beq (pc (FU.G (Nat.sub f 1)) X) (pc (BD.SG m) (FU.G (Nat.sub f 1))),
      bAnd(Nat.beq (pc (BD.SG m) (EL.G 1)) (pc (EL.G 1) (BD.SG m)),
        Nat.beq (pc (BD.SG m) (EL.G 2)) (pc (EL.G 2) (BD.SG m))))))))

@[expose] noncomputable def crOK (CR E : Nat → Nat) (i : Nat) : Bool :=
  strictB (CR i) (fun r => strictB (E i) (fun u =>
    bAnd(bIf(Nat.beq fld(r, 0, 1) 1, true, strictB (BD.SG fld(r, 1, 7)) (fun s =>
        strictB fld(r, 4, 511) (fun p => bAnd(Nat.blt p 480,
          bIf(Nat.beq (ip u (ip s p)) (ip s (ip u p)), false, true))))),
    bIf(Nat.beq fld(r, 13, 1) 0, strictB fld(r, 14, 511) (fun q => bAnd(Nat.blt q 480,
        bIf(Nat.beq (ip u (ip u q)) q, false, true))),
      bIf(Nat.beq fld(r, 23, 1) 0, Nat.beq u (BD.ZT fld(r, 24, 3)),
        bAnd(neAt u (EL.G 0) fld(r, 26, 511),
          allN 8 (fun l => Nat.beq (pc u (L.G l)) (pc (L.G l) u))))))))

@[expose] noncomputable def wit0c (c : Nat) : Bool :=
  allN 64 (fun d => witOK E0.T 4096 BD.W0 (Nat.add (Nat.mul 64 c) d))

@[expose] noncomputable def q80c (c : Nat) : Bool :=
  allN 16 (fun d => q8Row E0.T BD.RT0 BD.PR0 BD.LhG BD.LhI 73 BD.nR0 true (Nat.add (Nat.mul 16 c) d))

@[expose] noncomputable def q82c (c : Nat) : Bool :=
  allN 16 (fun d => q8Row E2.T BD.RT2 BD.PR2 BD.LcG BD.LcI 31 BD.nR2 false (Nat.add (Nat.mul 16 c) d))

end CertificateChecks.KernelOm2

end
