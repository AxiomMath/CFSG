module

public import Certificates.Kernel.HeLoc.FiveLDefs
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.FiveL

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KC.HeLoc CertificateChecks.KernelSpor

theorem kPerm : allN 13 (fun k => permOK 8330 14 (mask 14) (8330 * 14) (A k) (AI k)) = true := by
  quickRfl

theorem kNF : allN 13 (fun k => bAnd(nfValidK 5 HeC.LR (NF5.getD k 0), Nat.blt (FL5.getD k 0) 2)) =
    true := by
  quickRfl

theorem kN : Nat.beq Q.N 25 = true := by quickRfl

theorem kTree : allN 25 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 Q.P Q.L i)) = true := by
  quickRfl

theorem kReplay : CFSG.KC.Bfs.replayOK QE 2 25 = true := by quickRfl

theorem kEdge : allN 25 (edgeAtK pa q0 Q.P Q.L QE 25 25 2 Five.bs) = true := by quickRfl

theorem kSort : allN 25 (sortAtK qkey Q.SK Q.SKI 25) = true := by quickRfl

theorem kPow : allN 25 (fun i => eqOnL Five.bs (powF (qv i) 5) (fun x => x)) = true := by quickRfl

theorem kCover : allN 25 coverAt = true := by quickRfl

theorem kDist : allN 6 (fun j => allN 6 (distAt j)) = true := by quickRfl

theorem kLine : allN 6 lineAt = true := by quickRfl

theorem kId : Nat.beq (A 2) (pidn 8330 14) = true := by quickRfl

end CertificateChecks.KernelHeLoc.FiveL

#kss_each CertificateChecks.KernelHeLoc.FiveL.M5 CertificateChecks.KernelHeLoc.FiveL.memI 130

end
