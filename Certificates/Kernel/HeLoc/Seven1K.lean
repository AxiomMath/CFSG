module

public import Certificates.Kernel.HeLoc.Seven1Data
public import Certificates.Kernel.HeLoc.Seven1Tab
public import Certificates.Kernel.HeLoc.SevenDefs
public import Certificates.Data.Kernel.HeLoc.PTail
public import CFSG.Certificates.Kernel.HeLoc.GroupTabSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.HeLoc.GroupBfsSound
public import CFSG.Certificates.Kernel.HeLoc.TreeSound
public import Certificates.Data.Kernel.SporSch.PairHeCnt

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc

@[expose] noncomputable def gC1 (k x : Nat) : Nat := pa (Nat.add 65 k) x

@[expose] noncomputable def gD1 (l x : Nat) : Nat :=
  nIf(Nat.beq l 0, pa 66 (pa 67 (pi 66 (pi 67 x))), pa 67 x)

@[expose] noncomputable def CE1 (i k : Nat) : Nat := fld(C1.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def DE1 (i k : Nat) : Nat := fld(D1.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def cv1 (i x : Nat) : Nat := trV gC1 C1.P C1.L 1176 i x

@[expose] noncomputable def dv1 (i x : Nat) : Nat := trV gD1 D1.P D1.L 168 i x

@[expose] noncomputable def ckey1 (i : Nat) : Nat :=
  keyV 8330 CFSG.RankThree.PartOne.heSevenKeys (cv1 i)

@[expose] noncomputable def dkey1 (i : Nat) : Nat :=
  keyV 8330 CFSG.RankThree.PartOne.heSevenKeys (dv1 i)

@[expose] noncomputable def x1 (y : Nat) : Nat := ln 1 y

@[expose] noncomputable def relAt1 (r : Nat × Nat × Nat) : Bool :=
  bAnd(Nat.blt r.2.2 7, bAnd(Nat.blt r.1 10, bAnd(Nat.blt r.2.1 10,
    Nat.beq (powF x1 r.2.2 (CFSG.RankThree.PartOne.heSevenCase1BaseArr[r.1]!))
      (CFSG.RankThree.PartOne.heSevenCase1BaseArr[r.2.1]!))))

@[expose] noncomputable def fr1 (i : Nat) : Nat := FR1.getD i 0

@[expose] noncomputable def mt1 (a b : Nat) : Nat := fld(MT1 a, Nat.mul 8 b, 255)

@[expose] noncomputable def iv1 (a : Nat) : Nat := fld(IV1 0, Nat.mul 8 a, 255)

@[expose] noncomputable def cj1 (j r : Nat) : Nat := mt1 (mt1 j r) (iv1 j)

@[expose] noncomputable def btP (t i : Nat) : Nat := fld(BT1 t, Nat.mul 20 i, 255)

@[expose] noncomputable def btL (t i : Nat) : Nat := fld(BT1 t, Nat.add (Nat.mul 20 i) 8, 255)

@[expose] noncomputable def btD (t i : Nat) : Nat := fld(BT1 t, Nat.add (Nat.mul 20 i) 16, 15)

@[expose] noncomputable def mtB (a : Nat) : Bool :=
  allN 168 fun b => bAnd(Nat.blt (mt1 a b) 168,
    eqOnL bs (dv1 (mt1 a b)) (fun y => dv1 a (dv1 b y)))

@[expose] noncomputable def btB (t : Nat) : Bool :=
  allN 168 fun i => bIf(Nat.beq i 0, true,
    bAnd(Nat.blt (btP t i) 168, bAnd(Nat.blt (btL t i) 168,
      bAnd(Nat.beq (btD t i) (Nat.succ (btD t (btP t i))),
        Nat.beq i (mt1 (cj1 (btL t i) (RP1.getD t 0)) (btP t i))))))

@[expose] noncomputable def zAt1 (c : Nat) : Bool :=
  strictB (ZW1.getD c 0) fun w => bIf(Nat.blt w 100,
    bAnd(Nat.blt 0 w, bAnd(Nat.blt w 3,
      !eqOnL bs (fun y => cv1 c (gD1 (Nat.sub w 1) y)) (fun y => gD1 (Nat.sub w 1) (cv1 c y)))),
    bAnd(Nat.blt (Nat.sub w 100) 7, eqOnL bs (cv1 c) (powF x1 (Nat.sub w 100))))

theorem kN1 : bAnd(Nat.beq C1.N 1176, Nat.beq D1.N 168) = true := by quickRfl

theorem kCTree1 : allN 1176 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 C1.P C1.L i)) = true := by
  quickRfl

theorem kCReplay1 : CFSG.KC.Bfs.replayOK CE1 3 1176 = true := by quickRfl

theorem kCEdge1 : allN 1176 (edgeAtK gC1 q0 C1.P C1.L CE1 1176 1176 3 bs) = true := by quickRfl

theorem kCSort1 : allN 1176 (sortAtK ckey1 C1.SK C1.SKI 1176) = true := by quickRfl

theorem kDTree1 : allN 168 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 D1.P D1.L i)) = true := by
  quickRfl

theorem kDReplay1 : CFSG.KC.Bfs.replayOK DE1 2 168 = true := by quickRfl

theorem kDEdge1 : allN 168 (edgeAtK gD1 q0 D1.P D1.L DE1 168 168 2 bs) = true := by quickRfl

theorem kDSort1 : allN 168 (sortAtK dkey1 D1.SK D1.SKI 168) = true := by quickRfl

theorem kRels1 : CFSG.RankThree.PartOne.heSevenCase1Rels.all relAt1 = true := by quickRfl

theorem kComm1 : allN 3 (fun k => eqOnL bs (fun y => gC1 k (x1 y)) (fun y => x1 (gC1 k y))) =
    true := by quickRfl

theorem kFR1 : allN 10 (fun i => bIf(Nat.beq (fr1 i) 0, true,
    bAnd(Nat.blt (Nat.div (Nat.sub (fr1 i) 1) 8) i, bAnd(Nat.blt (Nat.mod (Nat.sub (fr1 i) 1) 8) 7,
      CFSG.RankThree.PartOne.heSevenCase1Rels.any fun r =>
        bAnd(Nat.beq r.1 (Nat.div (Nat.sub (fr1 i) 1) 8), bAnd(Nat.beq r.2.1 i,
          Nat.beq r.2.2 (Nat.mod (Nat.sub (fr1 i) 1) 8))))))) = true := by
  quickRfl

theorem kCD1 : allN 2 (fun i => bAnd(Nat.blt (CD1.getD i 0) 1176,
    eqOnL bs (cv1 (CD1.getD i 0)) (pa (Nat.add 68 i)))) = true := by quickRfl

theorem kCom1 : eqOnL bs (pa 67) (fun y => pa 68 (pa 69 (pi 68 (pi 69 y)))) = true := by quickRfl

theorem kDK1 : allN 6 (fun m => bAnd(Nat.blt (DK1.getD m 0) 168,
    eqOnL bs (dv1 (DK1.getD m 0)) (fun y => gC1 (Nat.div m 2) (gD1 (Nat.mod m 2)
      (pi (Nat.add 65 (Nat.div m 2)) y))))) = true := by quickRfl

theorem kDC1 : allN 9 (fun m => bAnd(Nat.blt (DC1.getD m 0) 168,
    eqOnL bs (dv1 (DC1.getD m 0)) (fun y => gC1 (Nat.div m 3) (gC1 (Nat.mod m 3)
      (pi (Nat.add 65 (Nat.div m 3)) (pi (Nat.add 65 (Nat.mod m 3)) y)))))) = true := by
  quickRfl

theorem kNC1 : (!eqOnL bs (fun y => gD1 0 (gD1 1 y)) (fun y => gD1 1 (gD1 0 y))) = true := by
  quickRfl

theorem kZ1 : allN 1176 zAt1 = true := by quickRfl

theorem kIV1 : allN 168 (fun a => bAnd(Nat.blt (iv1 a) 168,
    eqOnL bs (fun y => dv1 (iv1 a) (dv1 a y)) (fun y => y))) = true := by quickRfl

theorem kRP1 : (classRepsI 168 0 cj1 == RP1) = true := by quickRfl

theorem kCover1 : bAnd(RP1.all (fun r => Nat.blt r 168), allN 168 fun k =>
    (k == 0 || RP1.any fun r => (List.range 168).any fun j => k == cj1 j r)) = true := by
  quickRfl

theorem kBT1 : allN RP1.length btB = true := by quickRfl

theorem kTail1 : ptK 8330 14 11 T71.NR T71.NR T71.LT T71.PT T71.QT S71.LR fr1
    CFSG.RankThree.PartOne.heSevenCase1Rels x1 bs CFSG.RankThree.PartOne.heSevenKeys ckey1 C1.SK
    1176 10 0 (fun y => y) (fun y => y) (fun _ => 0) = true := by
  quickRfl

end CertificateChecks.KernelHeLoc.Seven

#kss_each CertificateChecks.KernelHeLoc.Seven.MTC1 CertificateChecks.KernelHeLoc.Seven.mtB 168

end
