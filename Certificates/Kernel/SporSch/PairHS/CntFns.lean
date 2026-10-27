module

public import Certificates.Kernel.SporSch.PairHS.CntData
public import Certificates.Kernel.SporSch.PairHS.ClFns

public section

namespace CertificateChecks.KernelSporSch.PHSCn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] def bs : List Nat := CFSG.Sporadic.Schreier.PairHS.bs

@[expose] noncomputable def nfp (F x : Nat) : Nat := nfPtT 12 PHST.NR PHST.NR PHST.LT PHST.PT 4 F x

@[expose] noncomputable def tAP (x : Nat) : Nat := pg 12 (mask 12) PHSN.T0 x

@[expose] noncomputable def tBP (x : Nat) : Nat := pg 12 (mask 12) PHSN.T1 x

@[expose] noncomputable def aP (x : Nat) : Nat := pg 12 (mask 12) PHSN.T2 x

@[expose] noncomputable def bP (x : Nat) : Nat := pg 12 (mask 12) PHSN.T3 x

@[expose] noncomputable def cP (x : Nat) : Nat := pg 12 (mask 12) PHSN.T4 x

@[expose] noncomputable def zP (x : Nat) : Nat := pg 12 (mask 12) PHSN.T5 x

@[expose] noncomputable def ziP (x : Nat) : Nat := pg 12 (mask 12) PHSN.T6 x

@[expose] noncomputable def wordP (RP : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun P _ ih x => ih (pg 12 (mask 12) P x)) RP x

@[expose] noncomputable def srAt (X Y : Nat → Nat) (q : Nat) : Nat :=
  srchR 12 8 PHST.NR PHST.NR PHST.LT PHST.PT PHST.QT PHSC.LR bs (nat_lit 0) X Y
    (Nat.mul q (nat_lit 154)) (nat_lit 154)

@[expose] noncomputable def srA (g r : Nat) : Bool :=
  Nat.beq (srAt aP aP (Nat.add (Nat.mul g 5) r)) (PHSN.V0 (Nat.add (Nat.mul g 5) r))

@[expose] noncomputable def srB (g r : Nat) : Bool :=
  Nat.beq (srAt bP bP (Nat.add (Nat.mul g 5) r)) (PHSN.V1 (Nat.add (Nat.mul g 5) r))

@[expose] noncomputable def srC (g r : Nat) : Bool :=
  Nat.beq (srAt cP cP (Nat.add (Nat.mul g 5) r)) (PHSN.V2 (Nat.add (Nat.mul g 5) r))

@[expose] noncomputable def srZ (g r : Nat) : Bool :=
  Nat.beq (srAt zP zP (Nat.add (Nat.mul g 5) r)) (PHSN.V3 (Nat.add (Nat.mul g 5) r))

@[expose] noncomputable def srZI (g r : Nat) : Bool :=
  Nat.beq (srAt zP ziP (Nat.add (Nat.mul g 5) r)) (PHSN.V4 (Nat.add (Nat.mul g 5) r))

@[expose] noncomputable def scAt (X : Nat → Nat) (c : Nat) (Z ZI : Nat → Nat) (q : Nat) : Nat :=
  scanHSR 12 PHST.NR PHST.NR PHST.LT PHST.PT bs c X Z ZI (Nat.mul q (nat_lit 512)) (nat_lit 512)

@[expose] noncomputable def scA (g r : Nat) : Bool :=
  Nat.beq (scAt PHSCl.XA PHST.c zP ziP (Nat.add (Nat.mul g 4) r))
    (PHSN.SC0 (Nat.add (Nat.mul g 4) r))

@[expose] noncomputable def scB (g r : Nat) : Bool :=
  Nat.beq (scAt PHSCl.XB PHSU.c zP ziP (Nat.add (Nat.mul g 4) r))
    (PHSN.SC1 (Nat.add (Nat.mul g 4) r))

@[expose] noncomputable def scAI (g r : Nat) : Bool :=
  Nat.beq (scAt PHSCl.XA PHST.c ziP zP (Nat.add (Nat.mul g 4) r))
    (PHSN.SC2 (Nat.add (Nat.mul g 4) r))

@[expose] noncomputable def scBI (g r : Nat) : Bool :=
  Nat.beq (scAt PHSCl.XB PHSU.c ziP zP (Nat.add (Nat.mul g 4) r))
    (PHSN.SC3 (Nat.add (Nat.mul g 4) r))

@[expose] noncomputable def invA (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 4) r) (nat_lit 512))
    (invAt 12 PHST.NR PHST.NR PHST.LT PHST.PT PHSC.LR bs PHST.c PHSCl.XA) (nat_lit 512)

@[expose] noncomputable def invB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 4) r) (nat_lit 512))
    (invAt 12 PHST.NR PHST.NR PHST.LT PHST.PT PHSC.LR bs PHSU.c PHSCl.XB) (nat_lit 512)

@[expose] noncomputable def r2 (i : Nat) : Nat := rowGet PHSN.R2 64 i

@[expose] noncomputable def par2 (i : Nat) : Nat := Nat.mod (rowGet PHSN.P2 16 i) 4096

@[expose] noncomputable def lab2 (i : Nat) : Nat := Nat.div (rowGet PHSN.P2 16 i) 4096

@[expose] noncomputable def gr2 (l : Nat) : Nat := PHSN.G2 l

@[expose] noncomputable def m2 (i l : Nat) : Nat := rowGet PHSN.M2 12 (Nat.add (Nat.mul i 3) l)

@[expose] noncomputable def d2 (i : Nat) : Nat := rowGet PHSN.D2 64 i

@[expose] noncomputable def c2 (i : Nat) : Nat := rowGet PHSN.C2 2 i

@[expose] noncomputable def tSel (c x : Nat) : Nat := nIf(Nat.beq c 0, tAP x, tBP x)

@[expose] noncomputable def K2 (i : Nat) : Nat := keyL 3850 (nfp (r2 i)) bs

@[expose] noncomputable def s2At (i : Nat) : Bool :=
  bAnd(nfValidK 4 PHSC.LR (r2 i),
  bAnd(bIf(Nat.blt 0 i, bAnd(Nat.blt (par2 i) i, bAnd(Nat.blt (lab2 i) 3,
      eqOnL bs (nfp (r2 i)) (fun b => nfp (r2 (par2 i)) (nfp (r2 (gr2 (lab2 i))) b)))),
    eqOnL bs (nfp (r2 i)) (fun x => x)),
  bAnd(allN 3 (fun l => bAnd(Nat.blt (m2 i l) 512,
    eqOnL bs (fun b => nfp (r2 i) (nfp (r2 (gr2 l)) b)) (nfp (r2 (m2 i l))))),
  bIf(ordPL bs (nfp (r2 i)) 2, bAnd(nfValidK 4 PHSC.LR (d2 i),
    eqOnL bs (fun b => nfp (d2 i) (tSel (c2 i) b)) (fun b => nfp (r2 i) (nfp (d2 i) b))), true))))

@[expose] noncomputable def s2B (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) (nat_lit 8)) s2At (nat_lit 8)

@[expose] noncomputable def srt2 (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) (nat_lit 8))
    (keySortAt [(512, K2)] (rowGet PHSN.O2 12) (rowGet PHSN.OI2 12) 512) (nat_lit 8)

@[expose] noncomputable def r5 (i : Nat) : Nat := rowGet PHSN.R5 64 i

@[expose] noncomputable def par5 (i : Nat) : Nat := Nat.mod (rowGet PHSN.P5 16 i) 4096

@[expose] noncomputable def lab5 (i : Nat) : Nat := Nat.div (rowGet PHSN.P5 16 i) 4096

@[expose] noncomputable def gr5 (l : Nat) : Nat := PHSN.G5 l

@[expose] noncomputable def m5 (i l : Nat) : Nat := rowGet PHSN.M5 12 (Nat.add (Nat.mul i 2) l)

@[expose] noncomputable def d5 (i : Nat) : Nat := rowGet PHSN.D5 64 i

@[expose] noncomputable def c5 (i : Nat) : Nat := rowGet PHSN.C5 2 i

@[expose] noncomputable def ySel (c x : Nat) : Nat := nIf(Nat.beq c 0, aP x, nIf(Nat.beq c 1, bP x, cP x))

@[expose] noncomputable def K5 (i : Nat) : Nat := keyL 3850 (nfp (r5 i)) bs

@[expose] noncomputable def s5At (i : Nat) : Bool :=
  bAnd(nfValidK 4 PHSC.LR (r5 i),
  bAnd(bIf(Nat.blt 0 i, bAnd(Nat.blt (par5 i) i, bAnd(Nat.blt (lab5 i) 2,
      eqOnL bs (nfp (r5 i)) (fun b => nfp (r5 (par5 i)) (nfp (r5 (gr5 (lab5 i))) b)))),
    eqOnL bs (nfp (r5 i)) (fun x => x)),
  bAnd(allN 2 (fun l => bAnd(Nat.blt (m5 i l) 125,
    eqOnL bs (fun b => nfp (r5 i) (nfp (r5 (gr5 l)) b)) (nfp (r5 (m5 i l))))),
  bIf(ordPL bs (nfp (r5 i)) 5, bAnd(nfValidK 4 PHSC.LR (d5 i),
    bAnd(Nat.blt (c5 i) 3,
    eqOnL bs (fun b => nfp (d5 i) (ySel (c5 i) b)) (fun b => nfp (r5 i) (nfp (d5 i) b)))), true))))

@[expose] noncomputable def s5B (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 5) r) (nat_lit 5)) s5At (nat_lit 5)

@[expose] noncomputable def srt5 (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 5) r) (nat_lit 5))
    (keySortAt [(125, K5)] (rowGet PHSN.O5 12) (rowGet PHSN.OI5 12) 125) (nat_lit 5)

@[expose] noncomputable def gensB : Bool :=
  bAnd(allN 3 (fun l => Nat.blt (gr2 l) 512), allN 2 (fun l => Nat.blt (gr5 l) 125))

@[expose] noncomputable def validB : Bool :=
  bAnd(nfValidK 4 PHSC.LR PHSN.n0, bAnd(nfValidK 4 PHSC.LR PHSN.n1,
  bAnd(nfValidK 4 PHSC.LR PHSN.n2, bAnd(nfValidK 4 PHSC.LR PHSN.n3,
  bAnd(nfValidK 4 PHSC.LR PHSN.n4, bAnd(nfValidK 4 PHSC.LR PHSN.n5,
  bAnd(nfValidK 4 PHSC.LR PHSN.n6, nfValidK 4 PHSC.LR PHSN.n7)))))))

@[expose] noncomputable def ordsB : Bool :=
  bAnd(ordPL bs tAP 2, bAnd(ordPL bs tBP 2, bAnd(ordPL bs aP 5, bAnd(ordPL bs bP 5,
  bAnd(ordPL bs cP 5, ordPL bs zP 11)))))

@[expose] noncomputable def relsB : Bool :=
  bAnd(Nat.beq (aP 0) 1, bAnd(Nat.beq (bP 0) 1, bAnd(Nat.beq (cP 0) 1, bAnd(Nat.beq (zP 0) 1,
  bAnd(eqOnL bs (fun b => zP (ziP b)) (fun x => x),
    eqOnL bs (fun b => nfp PHSN.n7 (zP b)) (fun b => powF zP 3 (nfp PHSN.n7 b)))))))

@[expose] noncomputable def repsB : Bool := bAnd(validB, bAnd(ordsB, relsB))

@[expose] noncomputable def bindR (F P lo : Nat) : Bool :=
  allBlk lo (bindAt 3850 12 PHST.NR PHST.NR PHST.LT PHST.PT F P) (nat_lit 770)

@[expose] noncomputable def nfOf (g : Nat) : Nat :=
  nIf(Nat.beq g 0, PHSN.n0, nIf(Nat.beq g 1, PHSN.n1, nIf(Nat.beq g 2, PHSN.n2,
  nIf(Nat.beq g 3, PHSN.n3, nIf(Nat.beq g 4, PHSN.n4, nIf(Nat.beq g 5, PHSN.n5, PHSN.n6))))))

@[expose] noncomputable def permOf (g : Nat) : Nat :=
  nIf(Nat.beq g 0, PHSN.T0, nIf(Nat.beq g 1, PHSN.T1, nIf(Nat.beq g 2, PHSN.T2,
  nIf(Nat.beq g 3, PHSN.T3, nIf(Nat.beq g 4, PHSN.T4, nIf(Nat.beq g 5, PHSN.T5, PHSN.T6))))))

@[expose] noncomputable def bindB (g r : Nat) : Bool := bindR (nfOf g) (permOf g) (Nat.mul r 770)

@[expose] noncomputable def wordB (r : Nat) : Bool :=
  allBlk (Nat.mul r 770) (fun x => bAnd(Nat.beq (tAP x) (wordP PHSCl.RPA x),
    Nat.beq (tBP x) (wordP PHSCl.RPB x))) (nat_lit 770)

end CertificateChecks.KernelSporSch.PHSCn

end
