module

public import Certificates.Kernel.SporSch.PairJ3.CntData
public import Certificates.Kernel.SporSch.PairJ3.ClFns

public section

namespace CertificateChecks.KernelSporSch.PJ3Cn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] def bs : List Nat := CFSG.Sporadic.Schreier.PairJ3.bs

@[expose] noncomputable def nfp (F x : Nat) : Nat := nfPtT 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT 4 F x

@[expose] noncomputable def tP (x : Nat) : Nat := pg 13 (mask 13) PJ3N.T x

@[expose] noncomputable def aP (x : Nat) : Nat := pg 13 (mask 13) PJ3N.YA x

@[expose] noncomputable def bP (x : Nat) : Nat := pg 13 (mask 13) PJ3N.YB x

@[expose] noncomputable def zP (x : Nat) : Nat := pg 13 (mask 13) PJ3N.Z x

@[expose] noncomputable def z2P (x : Nat) : Nat := zP (zP x)

@[expose] noncomputable def srAt (X Y : Nat → Nat) (q : Nat) : Nat :=
  srchR 13 5 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT PJ3T.QT PJ3.LR bs (nat_lit 0) X Y
    (Nat.mul q (nat_lit 171)) (nat_lit 171)

@[expose] noncomputable def srT (g r : Nat) : Bool :=
  Nat.beq (srAt tP tP (Nat.add (Nat.mul g 6) r)) (PJ3N.VT (Nat.add (Nat.mul g 6) r))

@[expose] noncomputable def srA (g r : Nat) : Bool :=
  Nat.beq (srAt aP aP (Nat.add (Nat.mul g 6) r)) (PJ3N.VA (Nat.add (Nat.mul g 6) r))

@[expose] noncomputable def srB (g r : Nat) : Bool :=
  Nat.beq (srAt bP bP (Nat.add (Nat.mul g 6) r)) (PJ3N.VB (Nat.add (Nat.mul g 6) r))

@[expose] noncomputable def srZ (g r : Nat) : Bool :=
  Nat.beq (srAt zP zP (Nat.add (Nat.mul g 6) r)) (PJ3N.VZ (Nat.add (Nat.mul g 6) r))

@[expose] noncomputable def srZ2 (g r : Nat) : Bool :=
  Nat.beq (srAt zP z2P (Nat.add (Nat.mul g 6) r)) (PJ3N.VZ2 (Nat.add (Nat.mul g 6) r))

@[expose] noncomputable def scAt (Z : Nat → Nat) (q : Nat) : Nat :=
  scanR 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT bs PJ3T.c PJ3Cl.X Z (Nat.mul q (nat_lit 512))
    (nat_lit 512)

@[expose] noncomputable def scZ (g r : Nat) : Bool :=
  Nat.beq (scAt zP (Nat.add (Nat.mul g 4) r)) (PJ3N.SZ (Nat.add (Nat.mul g 4) r))

@[expose] noncomputable def scZ2 (g r : Nat) : Bool :=
  Nat.beq (scAt z2P (Nat.add (Nat.mul g 4) r)) (PJ3N.SZ2 (Nat.add (Nat.mul g 4) r))

@[expose] noncomputable def invB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 4) r) (nat_lit 512))
    (invAt 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT PJ3.LR bs PJ3T.c PJ3Cl.X) (nat_lit 512)

@[expose] noncomputable def r2 (i : Nat) : Nat := rowGet PJ3N.R2 64 i

@[expose] noncomputable def m2 (i j : Nat) : Nat := rowGet PJ3N.M2 7 (Nat.add (Nat.mul i 128) j)

@[expose] noncomputable def d2 (i : Nat) : Nat := rowGet PJ3N.D2 64 i

@[expose] noncomputable def s2At (i : Nat) : Bool :=
  bAnd(nfValidK 4 PJ3.LR (r2 i),
  bAnd(allN 128 (fun j => bAnd(Nat.blt (m2 i j) 128,
    eqOnL bs (fun b => nfp (r2 i) (nfp (r2 j) b)) (nfp (r2 (m2 i j))))),
  bAnd(allN 128 (fun j => bIf(Nat.blt i j, bIf(eqOnL bs (nfp (r2 i)) (nfp (r2 j)), false, true),
    true)),
  bIf(ordPL bs (nfp (r2 i)) 2, bAnd(nfValidK 4 PJ3.LR (d2 i),
    eqOnL bs (fun b => nfp (d2 i) (tP b)) (fun b => nfp (r2 i) (nfp (d2 i) b))), true))))

@[expose] noncomputable def s2B (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 4) r) (nat_lit 8)) s2At (nat_lit 8)

@[expose] noncomputable def r3 (i : Nat) : Nat := rowGet PJ3N.R3 64 i

@[expose] noncomputable def d3 (i : Nat) : Nat := rowGet PJ3N.D3 64 i

@[expose] noncomputable def c3 (i : Nat) : Nat := rowGet PJ3N.C3 1 i

@[expose] noncomputable def ySel (c x : Nat) : Nat := nIf(Nat.beq c 0, aP x, bP x)

@[expose] noncomputable def s3At (i : Nat) : Bool :=
  bAnd(nfValidK 4 PJ3.LR (r3 i),
  bAnd(eqOnL bs (fun b => nfp (r3 i) (bP b)) (fun b => bP (nfp (r3 i) b)),
  bAnd(allN 243 (fun j => bIf(Nat.blt i j, bIf(eqOnL bs (nfp (r3 i)) (nfp (r3 j)), false, true),
    true)),
  bIf(ordPL bs (nfp (r3 i)) 3, bAnd(nfValidK 4 PJ3.LR (d3 i),
    eqOnL bs (fun b => nfp (d3 i) (ySel (c3 i) b)) (fun b => nfp (r3 i) (nfp (d3 i) b))), true))))

@[expose] noncomputable def s3B (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 3) r) (nat_lit 27)) s3At (nat_lit 27)

@[expose] noncomputable def repsB : Bool :=
  bAnd(nfValidK 4 PJ3.LR PJ3N.nT, bAnd(nfValidK 4 PJ3.LR PJ3N.nYA,
  bAnd(nfValidK 4 PJ3.LR PJ3N.nYB, bAnd(nfValidK 4 PJ3.LR PJ3N.nZ,
  bAnd(nfValidK 4 PJ3.LR PJ3N.nNu,
  bAnd(ordPL bs tP 2, bAnd(ordPL bs aP 3, bAnd(ordPL bs bP 3, bAnd(ordPL bs zP 19,
  bAnd(Nat.beq (tP 0) 1, bAnd(Nat.beq (aP 0) 1, bAnd(Nat.beq (bP 0) 1, bAnd(Nat.beq (zP 0) 1,
    eqOnL bs (fun b => nfp PJ3N.nNu (zP b)) (fun b => powF zP 4 (nfp PJ3N.nNu b)))))))))))))))

@[expose] noncomputable def bindR (F P lo : Nat) : Bool :=
  allBlk lo (bindAt 6156 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT F P) (nat_lit 1026)

@[expose] noncomputable def bindB (g r : Nat) : Bool :=
  bIf(Nat.beq g 0, bindR PJ3N.nT PJ3N.T (Nat.mul r 1026),
  bIf(Nat.beq g 1, bindR PJ3N.nYA PJ3N.YA (Nat.mul r 1026),
  bIf(Nat.beq g 2, bindR PJ3N.nYB PJ3N.YB (Nat.mul r 1026),
    bindR PJ3N.nZ PJ3N.Z (Nat.mul r 1026))))

end CertificateChecks.KernelSporSch.PJ3Cn

end
