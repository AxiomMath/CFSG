module

public import Certificates.Kernel.RuFive.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.HeLoc.PTail
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Kernel.RuFive.Tab

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc

theorem kC1Tree : allN 300 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 C1.P C1.L i)) = true := by
  quickRfl

theorem kC1Replay : CFSG.KC.Bfs.replayOK CE1 3 300 = true := by quickRfl

theorem kC1Edge : allN 300 (edgeAtK gC1 q0 C1.P C1.L CE1 300 300 3 bs) = true := by quickRfl

theorem kC1Sort : allN 300 (sortAtK ckey1 C1.SK C1.SKI 300) = true := by quickRfl

theorem kDTree : allN 60 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 D0.P D0.L i)) = true := by
  quickRfl

theorem kDReplay : CFSG.KC.Bfs.replayOK DE 2 60 = true := by quickRfl

theorem kDEdge : allN 60 (edgeAtK gD q0 D0.P D0.L DE 60 60 2 bs) = true := by quickRfl

theorem kDSort : allN 60 (sortAtK dkey D0.SK D0.SKI 60) = true := by quickRfl

theorem kRels1 : CFSG.RankThree.PartOne.ruCase1Rels.all relAt1 = true := by quickRfl

theorem kComm1 : allN 3 (fun k => eqOnL bs (fun y => gC1 k (x1 y)) (fun y => x1 (gC1 k y))) =
    true := by
  quickRfl

theorem kEq1 : Nat.beq (F 67) (F 3) = true := by quickRfl

theorem kFR1 : allN 5 (fun i => bIf(Nat.beq (fr1 i) 0, true,
    bAnd(Nat.blt (Nat.div (Nat.sub (fr1 i) 1) 8) i, bAnd(Nat.blt (Nat.mod (Nat.sub (fr1 i) 1) 8) 5,
      CFSG.RankThree.PartOne.ruCase1Rels.any fun r =>
        bAnd(Nat.beq r.1 (Nat.div (Nat.sub (fr1 i) 1) 8), bAnd(Nat.beq r.2.1 i,
          Nat.beq r.2.2 (Nat.mod (Nat.sub (fr1 i) 1) 8))))))) = true := by
  quickRfl

theorem kCD : allN 2 (fun i => bAnd(Nat.blt (CD.getD i 0) 300,
    eqOnL bs (cv1 (CD.getD i 0)) (pa (Nat.add 73 i)))) = true := by quickRfl

theorem kCom : eqOnL bs (pa 69) (fun y => pa 73 (pa 74 (pi 73 (pi 74 y)))) = true := by quickRfl

theorem kDK : allN 6 (fun m => bAnd(Nat.blt (DK.getD m 0) 60,
    eqOnL bs (dv (DK.getD m 0)) (fun y => gC1 (Nat.div m 2) (gD (Nat.mod m 2)
      (pi (Nat.add 67 (Nat.div m 2)) y))))) = true := by quickRfl

theorem kDC : allN 9 (fun m => bAnd(Nat.blt (DC.getD m 0) 60,
    eqOnL bs (dv (DC.getD m 0)) (fun y => gC1 (Nat.div m 3)
      (gC1 (Nat.mod m 3) (pi (Nat.add 67 (Nat.div m 3))
        (pi (Nat.add 67 (Nat.mod m 3)) y)))))) = true := by
  quickRfl

theorem kNC : (!eqOnL bs (fun y => gD 0 (gD 1 y)) (fun y => gD 1 (gD 0 y))) = true := by
  quickRfl

theorem kZ1 : allN 300 zAt1 = true := by quickRfl

theorem kMT : allN 60 mtB = true := by quickRfl

theorem kIV : allN 60 (fun a => bAnd(Nat.blt (iv a) 60,
    eqOnL bs (fun y => dv (iv a) (dv a y)) (fun y => y))) = true := by quickRfl

theorem kBT : allN 60 btB = true := by quickRfl

theorem kTail1 : ptK 4060 12 10 T51.NR T51.NR T51.LT T51.PT T51.QT S51.LR fr1
    CFSG.RankThree.PartOne.ruCase1Rels x1 bs CFSG.RankThree.PartOne.ruFiveKeys ckey1 C1.SK
    300 5 0 (fun y => y) (fun y => y) (fun _ => 0) = true := by
  quickRfl

end CertificateChecks.KernelRuFive

end
