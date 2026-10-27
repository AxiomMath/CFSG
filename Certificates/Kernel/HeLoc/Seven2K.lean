module

public import Certificates.Kernel.HeLoc.Seven2Data
public import Certificates.Kernel.HeLoc.Seven2Tab
public import Certificates.Kernel.HeLoc.SevenDefs
public import Certificates.Data.Kernel.HeLoc.PTail
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.SporSch.PairHeCnt

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc

@[expose] noncomputable def gC2 (k x : Nat) : Nat := pa (Nat.add 70 k) x

@[expose] noncomputable def gA2 (k x : Nat) : Nat := pa (Nat.add 73 k) x

@[expose] noncomputable def CE2 (i k : Nat) : Nat := fld(C2.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def AE2 (i k : Nat) : Nat := fld(A2.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def cv2 (i x : Nat) : Nat := trV gC2 C2.P C2.L 98 i x

@[expose] noncomputable def av2 (i x : Nat) : Nat := trV gA2 A2.P A2.L 49 i x

@[expose] noncomputable def ckey2 (i : Nat) : Nat :=
  keyV 8330 CFSG.RankThree.PartOne.heSevenKeys (cv2 i)

@[expose] noncomputable def akey2 (i : Nat) : Nat :=
  keyV 8330 CFSG.RankThree.PartOne.heSevenKeys (av2 i)

@[expose] noncomputable def x2 (y : Nat) : Nat := ln 2 y

@[expose] noncomputable def relAt2 (r : Nat × Nat × Nat) : Bool :=
  bAnd(Nat.blt r.2.2 7, bAnd(Nat.blt r.1 7, bAnd(Nat.blt r.2.1 7,
    Nat.beq (powF x2 r.2.2 (CFSG.RankThree.PartOne.heSevenCase2BaseArr[r.1]!))
      (CFSG.RankThree.PartOne.heSevenCase2BaseArr[r.2.1]!))))

@[expose] noncomputable def sAt2 (c : Nat) : Bool :=
  strictB (SW2.getD c 0) fun w => bIf(Nat.blt w 100,
    bAnd(Nat.blt 0 w, bAnd(Nat.blt w 3,
      !eqOnL bs (fun y => cv2 c (gA2 (Nat.sub w 1) y)) (fun y => gA2 (Nat.sub w 1) (cv2 c y)))),
    bAnd(Nat.blt (Nat.sub w 100) 49, eqOnL bs (cv2 c) (av2 (Nat.sub w 100))))

@[expose] noncomputable def fr2 (i : Nat) : Nat := FR2.getD i 0

theorem kCTree2 : allN 98 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 C2.P C2.L i)) = true := by
  quickRfl

theorem kCReplay2 : CFSG.KC.Bfs.replayOK CE2 3 98 = true := by quickRfl

theorem kCEdge2 : allN 98 (edgeAtK gC2 q0 C2.P C2.L CE2 98 98 3 bs) = true := by quickRfl

theorem kCSort2 : allN 98 (sortAtK ckey2 C2.SK C2.SKI 98) = true := by quickRfl

theorem kATree2 : allN 49 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 A2.P A2.L i)) = true := by
  quickRfl

theorem kAReplay2 : CFSG.KC.Bfs.replayOK AE2 2 49 = true := by quickRfl

theorem kAEdge2 : allN 49 (edgeAtK gA2 q0 A2.P A2.L AE2 49 49 2 bs) = true := by quickRfl

theorem kASort2 : allN 49 (sortAtK akey2 A2.SK A2.SKI 49) = true := by quickRfl

theorem kRels2 : CFSG.RankThree.PartOne.heSevenCase2Rels.all relAt2 = true := by quickRfl

theorem kComm2 : allN 3 (fun k => eqOnL bs (fun y => gC2 k (x2 y)) (fun y => x2 (gC2 k y))) =
    true := by quickRfl

theorem kAinC2 : allN 2 (fun l => bAnd(Nat.blt (AW2.getD l 0) 98,
    eqOnL bs (cv2 (AW2.getD l 0)) (gA2 l))) = true := by quickRfl

theorem kConj2 : allN 6 (fun m => bAnd(Nat.blt (CW2.getD m 0) 49,
    eqOnL bs (av2 (CW2.getD m 0)) (fun y => gC2 (Nat.div m 2) (gA2 (Nat.mod m 2)
      (pi (Nat.add 70 (Nat.div m 2)) y))))) = true := by quickRfl

theorem kAPow2 : allN 49 (fun i => eqOnL bs (powF (av2 i) 7) (fun y => y)) = true := by quickRfl

theorem kACom2 : allN 2 (fun l => allN 2 fun l' =>
    eqOnL bs (fun y => gA2 l (gA2 l' y)) (fun y => gA2 l' (gA2 l y))) = true := by quickRfl

theorem kS2 : allN 98 sAt2 = true := by quickRfl

theorem kFR2 : allN 7 (fun i => bIf(Nat.beq (fr2 i) 0, true,
    bAnd(Nat.blt (Nat.div (Nat.sub (fr2 i) 1) 8) i, bAnd(Nat.blt (Nat.mod (Nat.sub (fr2 i) 1) 8) 7,
      CFSG.RankThree.PartOne.heSevenCase2Rels.any fun r =>
        bAnd(Nat.beq r.1 (Nat.div (Nat.sub (fr2 i) 1) 8), bAnd(Nat.beq r.2.1 i,
          Nat.beq r.2.2 (Nat.mod (Nat.sub (fr2 i) 1) 8))))))) = true := by
  quickRfl

theorem kTail2 : ptK 8330 14 10 T72.NR T72.NR T72.LT T72.PT T72.QT S72.LR fr2
    CFSG.RankThree.PartOne.heSevenCase2Rels x2 bs CFSG.RankThree.PartOne.heSevenKeys ckey2 C2.SK
    98 7 0 (fun y => y) (fun y => y) (fun _ => 0) = true := by
  quickRfl

end CertificateChecks.KernelHeLoc.Seven

end
