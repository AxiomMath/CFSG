module

public import Certificates.Kernel.HeLoc.FiveDData
public import Certificates.Kernel.HeLoc.FiveTab
public import Certificates.Kernel.HeLoc.FiveLDefs
public import Certificates.Data.Kernel.HeLoc.PTail
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.FiveL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc

@[expose] noncomputable def gD (l x : Nat) : Nat :=
  nIf(Nat.beq l 0, pa 9 (pa 10 (pi 9 (pi 10 x))), pa 10 x)

@[expose] noncomputable def DE (i k : Nat) : Nat := fld(D0.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def dv (i x : Nat) : Nat := trV gD D0.P D0.L 60 i x

@[expose] noncomputable def dkey (i : Nat) : Nat :=
  keyV 8330 CFSG.RankThree.PartOne.heFiveKeys (dv i)

@[expose] noncomputable def cq (i : Nat) : Nat := trQ Five.q Five.C0.P Five.C0.L 600 i

@[expose] noncomputable def x0 (y : Nat) : Nat := ln 0 y

@[expose] noncomputable def relAt (r : Nat × Nat × Nat) : Bool :=
  bAnd(Nat.blt r.2.2 5, bAnd(Nat.blt r.1 9, bAnd(Nat.blt r.2.1 9,
    Nat.beq (powF x0 r.2.2 (CFSG.RankThree.PartOne.heFiveCase0BaseArr[r.1]!))
      (CFSG.RankThree.PartOne.heFiveCase0BaseArr[r.2.1]!))))

@[expose] noncomputable def fr5 (i : Nat) : Nat := FR5.getD i 0

@[expose] noncomputable def mt (a b : Nat) : Nat := fld(MT0 a, Nat.mul 8 b, 255)

@[expose] noncomputable def iv (a : Nat) : Nat := fld(IV0 0, Nat.mul 8 a, 255)

@[expose] noncomputable def cj (j r : Nat) : Nat := mt (mt j r) (iv j)

@[expose] noncomputable def btP (t i : Nat) : Nat := fld(BT0 t, Nat.mul 20 i, 255)

@[expose] noncomputable def btL (t i : Nat) : Nat := fld(BT0 t, Nat.add (Nat.mul 20 i) 8, 255)

@[expose] noncomputable def btD (t i : Nat) : Nat := fld(BT0 t, Nat.add (Nat.mul 20 i) 16, 15)

@[expose] noncomputable def mtB (a : Nat) : Bool :=
  allN 60 fun b => bAnd(Nat.blt (mt a b) 60,
    eqOnL Five.bs (dv (mt a b)) (fun y => dv a (dv b y)))

@[expose] noncomputable def btB (t : Nat) : Bool :=
  bIf(Nat.beq t 0, true, allN 60 fun i => bIf(Nat.beq i 0, true,
    bAnd(Nat.blt (btP t i) 60, bAnd(Nat.blt (btL t i) 60,
      bAnd(Nat.beq (btD t i) (Nat.succ (btD t (btP t i))),
        Nat.beq i (mt (cj (btL t i) t) (btP t i)))))))

@[expose] noncomputable def zAt (c : Nat) : Bool :=
  strictB (ZW0.getD c 0) fun w => bIf(Nat.blt w 100,
    bAnd(Nat.blt 0 w, bAnd(Nat.blt w 3,
      !eqOnL Five.bs (fun y => Five.tv c (gD (Nat.sub w 1) y))
        (fun y => gD (Nat.sub w 1) (Five.tv c y)))),
    bAnd(Nat.blt (Nat.sub w 100) 5, bAnd(Nat.beq (cq c) 0,
      eqOnL Five.bs (Five.tv c) (powF x0 (Nat.sub w 100)))))

theorem kDTree : allN 60 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 D0.P D0.L i)) = true := by
  quickRfl

theorem kDReplay : CFSG.KC.Bfs.replayOK DE 2 60 = true := by quickRfl

theorem kDEdge : allN 60 (edgeAtK gD q0 D0.P D0.L DE 60 60 2 Five.bs) = true := by quickRfl

theorem kDSort : allN 60 (sortAtK dkey D0.SK D0.SKI 60) = true := by quickRfl

theorem kRels : CFSG.RankThree.PartOne.heFiveCase0Rels.all relAt = true := by quickRfl

theorem kComm : allN 3 (fun k => eqOnL Five.bs (fun y => Five.g k (x0 y))
    (fun y => x0 (Five.g k y))) = true := by quickRfl

theorem kFR : allN 9 (fun i => bIf(Nat.beq (fr5 i) 0, true,
    bAnd(Nat.blt (Nat.div (Nat.sub (fr5 i) 1) 8) i, bAnd(Nat.blt (Nat.mod (Nat.sub (fr5 i) 1) 8) 5,
      CFSG.RankThree.PartOne.heFiveCase0Rels.any fun r =>
        bAnd(Nat.beq r.1 (Nat.div (Nat.sub (fr5 i) 1) 8), bAnd(Nat.beq r.2.1 i,
          Nat.beq r.2.2 (Nat.mod (Nat.sub (fr5 i) 1) 8))))))) = true := by
  quickRfl

theorem kCD : allN 2 (fun i => bAnd(Nat.blt (CD0.getD i 0) 600,
    bAnd(Nat.beq (cq (CD0.getD i 0)) (FL5.getD (Nat.add 11 i) 0),
      eqOnL Five.bs (Five.tv (CD0.getD i 0)) (pa (Nat.add 11 i))))) = true := by quickRfl

theorem kCom : eqOnL Five.bs (pa 10) (fun y => pa 11 (pa 12 (pi 11 (pi 12 y)))) = true := by
  quickRfl

theorem kDK : allN 6 (fun m => bAnd(Nat.blt (DK0.getD m 0) 60,
    eqOnL Five.bs (dv (DK0.getD m 0)) (fun y => pa (Nat.add 8 (Nat.div m 2)) (gD (Nat.mod m 2)
      (pi (Nat.add 8 (Nat.div m 2)) y))))) = true := by quickRfl

theorem kDC : allN 9 (fun m => bAnd(Nat.blt (DC0.getD m 0) 60,
    eqOnL Five.bs (dv (DC0.getD m 0)) (fun y => pa (Nat.add 8 (Nat.div m 3))
      (pa (Nat.add 8 (Nat.mod m 3)) (pi (Nat.add 8 (Nat.div m 3))
        (pi (Nat.add 8 (Nat.mod m 3)) y)))))) = true := by
  quickRfl

theorem kNC : (!eqOnL Five.bs (fun y => gD 0 (gD 1 y)) (fun y => gD 1 (gD 0 y))) = true := by
  quickRfl

theorem kZ : allN 600 zAt = true := by quickRfl

theorem kMT : allN 60 mtB = true := by quickRfl

theorem kIV : allN 60 (fun a => bAnd(Nat.blt (iv a) 60,
    eqOnL Five.bs (fun y => dv (iv a) (dv a y)) (fun y => y))) = true := by quickRfl

theorem kBT : allN 60 btB = true := by quickRfl

theorem kTail : ptK 8330 14 11 T50.NR T50.NR T50.LT T50.PT T50.QT S50.LR fr5
    CFSG.RankThree.PartOne.heFiveCase0Rels x0 Five.bs CFSG.RankThree.PartOne.heFiveKeys Five.key
    Five.C0.SK 600 9 0 (fun y => y) (fun y => y) (fun _ => 0) = true := by
  quickRfl

end CertificateChecks.KernelHeLoc.FiveL

end
