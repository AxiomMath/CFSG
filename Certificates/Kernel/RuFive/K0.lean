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

theorem kCTree : allN 1000 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 C0.P C0.L i)) = true := by
  quickRfl

theorem kCReplay : CFSG.KC.Bfs.replayOK CE 3 1000 = true := by quickRfl

theorem kCEdge : allN 1000 (edgeAtK gC q0 C0.P C0.L CE 1000 1000 3 bs) = true := by quickRfl

theorem kCSort : allN 1000 (sortAtK ckey C0.SK C0.SKI 1000) = true := by quickRfl

theorem kATree : allN 125 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 A0.P A0.L i)) = true := by
  quickRfl

theorem kAReplay : CFSG.KC.Bfs.replayOK AE 3 125 = true := by quickRfl

theorem kAEdge : allN 125 (edgeAtK gA q0 A0.P A0.L AE 125 125 3 bs) = true := by quickRfl

theorem kASort : allN 125 (sortAtK akey A0.SK A0.SKI 125) = true := by quickRfl

theorem kRels0 : CFSG.RankThree.PartOne.ruCase0Rels.all relAt0 = true := by quickRfl

theorem kComm0 : allN 3 (fun k => eqOnL bs (fun y => gC k (x0 y)) (fun y => x0 (gC k y))) = true := by
  quickRfl

theorem kEq0 : Nat.beq (F 64) (F 2) = true := by quickRfl

theorem kFR0 : allN 9 (fun i => bIf(Nat.beq (fr0 i) 0, true,
    bAnd(Nat.blt (Nat.div (Nat.sub (fr0 i) 1) 8) i, bAnd(Nat.blt (Nat.mod (Nat.sub (fr0 i) 1) 8) 5,
      CFSG.RankThree.PartOne.ruCase0Rels.any fun r =>
        bAnd(Nat.beq r.1 (Nat.div (Nat.sub (fr0 i) 1) 8), bAnd(Nat.beq r.2.1 i,
          Nat.beq r.2.2 (Nat.mod (Nat.sub (fr0 i) 1) 8))))))) = true := by
  quickRfl

theorem kAinC : allN 3 (fun l => bAnd(Nat.blt (AW.getD l 0) 1000,
    eqOnL bs (cv (AW.getD l 0)) (gA l))) = true := by
  quickRfl

theorem kConj : allN 9 (fun m => bAnd(Nat.blt (CW.getD m 0) 125,
    eqOnL bs (av (CW.getD m 0)) (fun y => gC (Nat.div m 3) (gA (Nat.mod m 3)
      (pi (Nat.add 64 (Nat.div m 3)) y))))) = true := by
  quickRfl

theorem kAPow : allN 125 (fun i => eqOnL bs (powF (av i) 5) (fun y => y)) = true := by quickRfl

theorem kXinA : bAnd(Nat.blt (XW.getD 0 0) 125, eqOnL bs (av (XW.getD 0 0)) x0) = true := by
  quickRfl

theorem kZ0 : allN 1000 zAt0 = true := by quickRfl

theorem kTail0 : ptK 4060 12 8 T50.NR T50.NR T50.LT T50.PT T50.QT S50.LR fr0
    CFSG.RankThree.PartOne.ruCase0Rels x0 bs CFSG.RankThree.PartOne.ruFiveKeys ckey C0.SK
    1000 9 0 (fun y => y) (fun y => y) (fun _ => 0) = true := by
  quickRfl

end CertificateChecks.KernelRuFive

end
