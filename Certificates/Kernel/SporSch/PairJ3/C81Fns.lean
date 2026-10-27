module

public import Certificates.Kernel.SporSch.PairJ3.C81Data

public section

namespace CertificateChecks.KernelSporSch.PJ3C81

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] noncomputable def cP (k x : Nat) : Nat := pg 13 (mask 13) (C81T.P k) x

@[expose] noncomputable def cI (k x : Nat) : Nat := pg 13 (mask 13) (C81T.I k) x

@[expose] noncomputable def sP (j x : Nat) : Nat := pg 13 (mask 13) (PJ3.S j) x

@[expose] def bs : List Nat := PJ3Cn.bs

@[expose] noncomputable def nfp (F x : Nat) : Nat := PJ3Cn.nfp F x

@[expose] noncomputable def nfi (F x : Nat) : Nat :=
  strictN (trInvPtT 13 5 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT (nat_lit 0) fld(F, nat_lit 0, nat_lit 65535) x)
    (fun y => strictN (trInvPtT 13 5 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT (nat_lit 1)
      fld(F, nat_lit 16, nat_lit 65535) y)
    (fun z => strictN (trInvPtT 13 5 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT (nat_lit 2)
      fld(F, nat_lit 32, nat_lit 65535) z)
    (fun v => trInvPtT 13 5 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT (nat_lit 3)
      fld(F, nat_lit 48, nat_lit 65535) v)))

@[expose] noncomputable def uP (b x : Nat) : Nat := nIf(Nat.beq b 0, x, cP 0 x)

@[expose] noncomputable def bMap (g x : Nat) : Nat :=
  nIf(Nat.blt g 6, cP (nIf(Nat.beq g 0, 9, Nat.add g 9)) x,
  nIf(Nat.beq g 6, cP 21 (cP 0 x),
  nIf(Nat.blt g 10, cP (Nat.add g 15) x,
  nIf(Nat.beq g 10, cP 0 (sP 0 (cP 0 x)),
  nIf(Nat.beq g 11, cP 0 (sP 1 (cP 0 x)),
  nIf(Nat.beq g 15, cP 4 (cP 0 x),
  nIf(Nat.beq g 18, cP 7 (cP 0 x), cP (Nat.sub g 11) x)))))))

@[expose] def bNFs : List Nat := [65536, 65536, 281474999390686, 4295164532, 562949970266780,
  281475058302976, 32508486, 65536, 4295164532, 281479306155838, 4361486336, 82515896,
  65536, 4295164532, 562950025122992, 281475043563362, 562954286530692, 562954260512768,
  281475013613410, 281475038515107]

@[expose] noncomputable def bNF (g : Nat) : Nat := bNFs.getD g 0

@[expose] noncomputable def bindB (g r : Nat) : Bool :=
  allBlk (Nat.mul r (nat_lit 1026)) (fun x => Nat.beq (bMap g x) (nfp (bNF g) x)) (nat_lit 1026)

@[expose] noncomputable def eP (i x : Nat) : Nat := nfp (C81D.SN i) (uP (C81D.SB i) x)

@[expose] noncomputable def gB (j : Nat) : Nat := nIf(Nat.beq j 3, 1, nIf(Nat.beq j 6, 1, 0))

@[expose] noncomputable def gP (j x : Nat) : Nat := cP (Nat.add j 1) x

@[expose] noncomputable def xorB (a b : Nat) : Nat := nIf(Nat.beq a b, 0, 1)

@[expose] noncomputable def eqProd (m j i : Nat) : Bool :=
  bAnd(Nat.beq (C81D.SB m) (xorB (gB j) (C81D.SB i)),
    eqOnL bs (nfp (C81D.SN m)) (fun b => gP j (eP i (uP (C81D.SB m) b))))

@[expose] noncomputable def sKey (i : Nat) : Nat :=
  Nat.add (Nat.mul (C81D.SB i) (nat_lit 18446744073709551616)) (keyL 6156 (nfp (C81D.SN i)) bs)

@[expose] noncomputable def invW (i : Nat) : Bool :=
  bIf(Nat.beq (C81D.SW i) 1, bIf(eqOnL bs (fun x => eP i (eP i x)) (fun x => x), false, true),
    bAnd(Nat.beq (C81D.SW i) 2, bAnd(nfValidK 4 PJ3.LR (C81D.SX i),
      eqOnL bs (fun x => eP i (nfp (C81D.SX i) (cP 0 x)))
        (fun x => nfp (C81D.SX i) (cP 21 (cP 0 x))))))

@[expose] noncomputable def sAt (i : Nat) : Bool :=
  bAnd(nfValidK 4 PJ3.LR (C81D.SN i),
  bAnd(Nat.blt (C81D.SB i) 2,
  bAnd(bIf(Nat.beq i 0, bAnd(Nat.beq (C81D.SB 0) 0, eqOnL bs (nfp (C81D.SN 0)) (fun x => x)),
    bAnd(Nat.blt (C81D.SP i) i, bAnd(Nat.blt (C81D.SG i) 8, eqProd i (C81D.SG i) (C81D.SP i)))),
  bAnd(allN 8 (fun j => bAnd(Nat.blt (C81D.SM (Nat.add (Nat.mul i 8) j)) 256,
    eqProd (C81D.SM (Nat.add (Nat.mul i 8) j)) j i)),
  bAnd(Nat.blt (C81D.SO i) 256,
  bAnd(bIf(Nat.blt i 255, Nat.blt (sKey (C81D.SO i)) (sKey (C81D.SO (Nat.add i 1))), true),
    bIf(Nat.beq (C81D.SB i) 1, invW i, true)))))))

@[expose] noncomputable def sB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 2) r) (nat_lit 64)) sAt (nat_lit 64)

@[expose] noncomputable def o1At (k : Nat) : Bool :=
  bAnd(Nat.blt (C81D.O1P k) 6156, bAnd(Nat.beq (C81D.O1Q (C81D.O1P k)) k,
  bIf(Nat.beq k 0, Nat.beq (C81D.O1P 0) 1,
    bAnd(Nat.blt (C81D.O1R k) k, bAnd(Nat.blt (C81D.O1G k) 5,
      Nat.beq (C81D.O1P k) (cP (Nat.add 10 (C81D.O1G k)) (C81D.O1P (C81D.O1R k))))))))

@[expose] noncomputable def o2At (k : Nat) : Bool :=
  bAnd(Nat.blt (C81D.O2P k) 6156, bAnd(Nat.beq (C81D.O2Q (C81D.O2P k)) k,
  bIf(Nat.beq k 0, Nat.beq (C81D.O2P 0) 1,
    bAnd(Nat.blt (C81D.O2R k) k, bAnd(Nat.blt (C81D.O2G k) 3,
      Nat.beq (C81D.O2P k) (cP (Nat.add 22 (C81D.O2G k)) (C81D.O2P (C81D.O2R k))))))))

@[expose] noncomputable def w1 (x : Nat) : Nat := cI 14 (cI 11 (cP 12 (cP 11 (cP 12 x))))

@[expose] noncomputable def w2 (x : Nat) : Nat :=
  cI 23 (cI 24 (cI 22 (cI 24 (cP 23 (cP 24 (cP 22 (cP 24 (cP 23 x))))))))

@[expose] noncomputable def clKey (F : Nat) : Nat := keyL 6156 (fun b => nfp F (cP 21 (nfi F b))) bs

@[expose] noncomputable def clAt (i : Nat) : Bool :=
  bAnd(nfValidK 4 PJ3.LR (C81D.CL i), bAnd(Nat.beq (clKey (C81D.CL i)) (C81D.CK i),
    bIf(Nat.blt (Nat.add i 1) 20520, Nat.blt (C81D.CK i) (C81D.CK (Nat.add i 1)), true)))

@[expose] noncomputable def clB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 6) r) (nat_lit 570)) clAt (nat_lit 570)

@[expose] def stNFs : List Nat := [65536, 131072, 4294967296, 281474976710656]

@[expose] noncomputable def stAt (x : Nat) : Bool :=
  bIf(Nat.beq x 0, true, List.rec (motive := fun _ => Bool) false
    (fun F _ ih => bIf(Nat.beq (nfp F x) x, ih, true)) stNFs)

@[expose] def oddW : List (Nat × Nat × Nat × Nat × Nat) :=
  [(562954323755875, 562949970266780, 3, 3, 0), (281475052077923, 281474999390686, 5, 3, 0),
   (281474976714532, 4295361140, 17, 1, 1), (562954289616702, 45351538, 9, 1, 1)]

@[expose] noncomputable def commR (row : Nat) (f : Nat → Nat) : Bool :=
  bIf(Nat.beq row 0, eqOnL bs (fun x => f (cP 9 x)) (fun x => cP 9 (f x)),
    eqOnL bs (fun x => f (cP 21 (cP 0 x))) (fun x => cP 21 (f (cP 0 x))))

@[expose] noncomputable def oddOK (z h q m row : Nat) : Bool :=
  bAnd(nfValidK 4 PJ3.LR z, bAnd(nfValidK 4 PJ3.LR h,
  bAnd(bIf(Nat.beq q 9, ord9L bs (nfp z), ordPL bs (nfp z) q),
  bAnd(commR row (nfp z), bAnd(commR row (nfp h),
    (fun (w : Nat → Nat) =>
      (fun (y : Nat → Nat) => bAnd(eqOnL bs (powF y (Nat.mul 2 m)) (fun x => x),
        bIf(eqOnL bs (powF y m) (fun x => x), false, true)))
      (fun x => w (nfp h (w (nfi h x)))))
    (powF (nfp z) (nIf(Nat.beq q 9, 3, 1))))))))

@[expose] noncomputable def oddB : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => bAnd(oddOK e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2, ih)) oddW

@[expose] noncomputable def ptAt (x : Nat) : Bool :=
  bAnd(Nat.beq (cP 0 (cP 0 x)) x, bAnd(Nat.beq (cP 21 (cP 21 x)) x,
  bAnd(bIf(Nat.beq (cP 0 x) x, false, true), bAnd(bIf(Nat.beq (cP 21 x) x, false, true),
    stAt x))))

@[expose] noncomputable def smallB : Bool :=
  bAnd(allN 20 (fun g => nfValidK 4 PJ3.LR (bNF g)),
  bAnd(List.rec (motive := fun _ => Bool) true
    (fun F _ ih => bAnd(nfValidK 4 PJ3.LR F, bAnd(Nat.beq (nfp F 0) 0, ih))) stNFs,
  bAnd(Nat.beq (PJ3Cn.tP 107) 107,
  bAnd(ordPL bs (cP 9) 2,
  bAnd(allN 5 (fun j => commR 0 (cP (Nat.add 10 j))),
  bAnd(allN 3 (fun j => commR 1 (cP (Nat.add 22 j))),
  bAnd(Nat.beq (w1 1) 1, bAnd(bIf(Nat.beq (w1 3) 3, false, true),
  bAnd(Nat.beq (w2 1) 1, bAnd(bIf(Nat.beq (w2 0) 0, false, true), oddB))))))))))

end CertificateChecks.KernelSporSch.PJ3C81

end
