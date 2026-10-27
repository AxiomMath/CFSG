module

public import Certificates.Kernel.HeLoc.SevenDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.SporSch.PairHeCnt

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KC.HeLoc

theorem kTree : allN 343 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 Q.P Q.L i)) = true := by
  quickRfl

theorem kReplay : CFSG.KC.Bfs.replayOK QE 2 343 = true := by quickRfl

theorem kEdge : allN 343 (edgeAtK pa q0 Q.P Q.L QE 343 343 2 bs) = true := by quickRfl

theorem kSort : allN 343 (sortAtK qkey Q.SK Q.SKI 343) = true := by quickRfl

theorem kPow : allN 343 (fun i => eqOnL bs (powF (qv i) 7) (fun x => x)) = true := by quickRfl

theorem kCover : allN 343 coverAt = true := by quickRfl

theorem kDist0 : allN 19 (fun j => allN 57 (distAt j)) = true := by quickRfl

theorem kDist1 : allN 19 (fun j => allN 57 (distAt (Nat.add 19 j))) = true := by quickRfl

theorem kDist2 : allN 19 (fun j => allN 57 (distAt (Nat.add 38 j))) = true := by quickRfl

theorem kLine : allN 57 lineAt = true := by quickRfl

theorem kId : allN 3 (fun i => Nat.beq (A (Nat.add 2 i)) (pidn 8330 14)) = true := by quickRfl

end CertificateChecks.KernelHeLoc.Seven

end
