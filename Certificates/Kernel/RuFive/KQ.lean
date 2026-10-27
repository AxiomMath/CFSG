module

public import Certificates.Kernel.RuFive.Defs
public import Certificates.Kernel.Misc.RuInv.Data
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.HeLoc.PTail
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Kernel.RuFive.Tab

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KS.Prim

theorem kBind0 : allN 8 (fun j => Nat.beq (H50.F j) (S50.S j)) = true := by quickRfl

theorem kBind1 : allN 10 (fun j => Nat.beq (H51.F j) (S51.S j)) = true := by quickRfl

theorem kPerm0 : allN 8 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (S50.S j) (S50.SI j)) =
    true := by quickRfl

theorem kPerm1 : allN 10 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (S51.S j) (S51.SI j)) =
    true := by quickRfl

theorem kGen00 : Nat.beq (S50.S 0) CertificateChecks.KernelMisc.RuInv.AD.n0 = true := by quickRfl

theorem kGen01 : Nat.beq (S50.S 1) CertificateChecks.KernelMisc.RuInv.AD.n1 = true := by quickRfl

theorem kGen10 : Nat.beq (S51.S 0) CertificateChecks.KernelMisc.RuInv.AD.n0 = true := by quickRfl

theorem kGen11 : Nat.beq (S51.S 1) CertificateChecks.KernelMisc.RuInv.AD.n1 = true := by quickRfl

theorem kBase0 : allN 9 (fun t => Nat.beq CFSG.RankThree.PartOne.ruCase0BaseArr[t]!
    (pg 12 (mask 12) S50.BP t)) = true := by quickRfl

theorem kBase1 : allN 5 (fun t => Nat.beq CFSG.RankThree.PartOne.ruCase1BaseArr[t]!
    (pg 12 (mask 12) S51.BP t)) = true := by quickRfl

theorem kOrb0 : allN 9 (fun i => Nat.beq (rcnt (S50.LR i))
    ([4060, 1755, 1024, 4, 5, 1, 1, 1, 1].getD i 0)) = true := by quickRfl

theorem kOrb1 : allN 5 (fun i => Nat.beq (rcnt (S51.LR i)) ([4060, 1755, 1024, 20, 1].getD i 0)) =
    true := by quickRfl

theorem kPermF : allN 75 (fun k => permOK 4060 12 (mask 12) (4060 * 12) (F k) (AI k)) = true := by
  quickRfl

@[expose] noncomputable def wordB (c : Nat) : Bool :=
  allN 20 fun i => bIf(Nat.blt (Nat.add (Nat.mul 20 c) i) 75,
    wordEqK 4060 12 (mask 12) (pidn 4060 12) S50.S S50.SI 8 (wd (Nat.add (Nat.mul 20 c) i))
      (F (Nat.add (Nat.mul 20 c) i)), true)

end CertificateChecks.KernelRuFive

#kss_each CertificateChecks.KernelRuFive.WB CertificateChecks.KernelRuFive.wordB 4

namespace CertificateChecks.KernelRuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KS.Prim

theorem kQN : Nat.beq Q.N 125 = true := by quickRfl

theorem kQTree : allN 125 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 Q.P Q.L i)) = true := by
  quickRfl

theorem kQReplay : CFSG.KC.Bfs.replayOK QE 2 125 = true := by quickRfl

theorem kQEdge : allN 125 (edgeAtK gQ q0 Q.P Q.L QE 125 125 2 bs) = true := by quickRfl

theorem kQSort : allN 125 (sortAtK qkey Q.SK Q.SKI 125) = true := by quickRfl

theorem kQPow : allN 125 (fun i => eqOnL bs (powF (qv i) 5) (fun x => x)) = true := by quickRfl

theorem kCover : allN 125 coverAt = true := by quickRfl

theorem kDist : allN 31 (fun j => allN 31 (distAt j)) = true := by quickRfl

theorem kLine : allN 31 lineAt = true := by quickRfl

theorem kTrans : allN 31 transAt = true := by quickRfl

theorem kOrbNeg : (!allN 9 (fun i => Nat.beq (rcnt (S50.LR i))
    ([4060, 1755, 1024, 4, 5, 1, 1, 1, 2].getD i 0))) = true := by quickRfl

theorem kWordNeg : (!wordEqK 4060 12 (mask 12) (pidn 4060 12) S50.S S50.SI 8 (wd 0) (F 1)) = true := by
  quickRfl

theorem kDistNeg : (!distAt 1 1 || distAt 0 1) = true := by quickRfl

end CertificateChecks.KernelRuFive

end
