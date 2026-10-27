module

public import Certificates.Kernel.SporSch.HN.T0Data
public import Certificates.Kernel.SporSch.HN.PtC
public import Certificates.Data.Kernel.SporSch.HNT0P
public import CFSG.Certificates.Kernel.Local.HN.X.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSporSch.HNT0

open CFSG.KD.HNT0 CFSG.KS.HNT0 CFSG.KD.LgHNX CFSG.KC.LL.HNX

theorem om : omK 192 1140000 OM = true := by quickRfl

theorem rank : rankK 192 TX CM3 M RI OM RK = true := by quickRfl

theorem t4i : bAnd(Nat.blt T4I 16384, Nat.beq (T T4I) GT4) = true := by quickRfl

theorem pts_t4 : ptsK 192 TX MS CM3 M CFSG.KD.HNPtC.T4 OM GT4 = true := by quickRfl

theorem pts_w0 : ptsK 192 TX MS CM3 M (wordC CFSG.KD.HNPtC.GT [20, 3, 9, 9, 7, 20]) OM (G 0) =
    true := by quickRfl
theorem pts_w1 : ptsK 192 TX MS CM3 M (wordC CFSG.KD.HNPtC.GT [18, 20, 4]) OM (G 1) = true := by
  quickRfl
theorem pts_w2 : ptsK 192 TX MS CM3 M (wordC CFSG.KD.HNPtC.GT [20, 4, 9, 9, 6, 20]) OM (G 2) =
    true := by quickRfl
theorem pts_w3 : ptsK 192 TX MS CM3 M (wordC CFSG.KD.HNPtC.GT [5]) OM (G 3) = true := by quickRfl

theorem neg_om : Bool.not (omK 192 1140000 (OM.set 5 (OM.getD 7 0))) = true := by quickRfl
theorem neg_rank : Bool.not (rankK 192 TX CM3 M RI OM (RK.set 70 (RK.getD 71 0))) = true := by
  quickRfl
theorem neg_t4i : Bool.not (Nat.beq (T (Nat.succ T4I)) GT4) = true := by quickRfl
theorem neg_pts : Bool.not (ptsK 192 TX MS CM3 M CFSG.KD.HNPtC.T4 OM (G 0)) = true := by quickRfl
theorem neg_ptw : Bool.not (ptsK 192 TX MS CM3 M (wordC CFSG.KD.HNPtC.GT [18, 20, 4]) OM (G 2)) =
    true := by quickRfl

end CertificateChecks.KernelSporSch.HNT0

end
