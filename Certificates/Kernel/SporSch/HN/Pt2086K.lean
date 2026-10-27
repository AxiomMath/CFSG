module

public import Certificates.Kernel.SporSch.HN.PtC
public import Certificates.Kernel.SporSch.HN.Pt2086Data
public import Certificates.Data.Kernel.SporSch.HNXPt
public import CFSG.Certificates.Kernel.Local.HN.X.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2086

open CFSG.KC.LL.HNX CFSG.KD.HNPt2086 CFSG.KD.LgHNX CFSG.KC.LL

theorem w_WT : CFSG.KC.Enum.allN 14 (fun i => Nat.beq (wordC CFSG.KD.HNPtC.GT (pcF i)) (WT i)) =
    true := by quickRfl

theorem one_YT : Nat.beq (YT 0) CFSG.KD.OrdHN.ONE = true := by quickRfl

theorem chain_YT : CFSG.KC.Enum.allN 43 (fun k => Nat.beq (CFSG.KC.LL.HN.mm
    (WT (fldW CL (Nat.mul 4 (Nat.add k 1)) 4)) (YT (fldW CP (Nat.mul 6 (Nat.add k 1)) 6)))
    (YT (Nat.add k 1))) = true := by quickRfl

theorem p_T4 : ptsImg TX MS CM3 M (trM CFSG.KD.HNPtC.T4) FT UT 40 = true := by quickRfl

theorem p_reps : CFSG.KC.Enum.allN 29 (fun c =>
    ptsImg TX MS CM3 M (trM (YT (fldW KP (Nat.mul 6 c) 6))) (PF c) (PI c) 2) = true := by quickRfl

theorem p_wits : CFSG.KC.Enum.allN 39 (fun w =>
    ptsImg TX MS CM3 M (trM (YT (fldW WK (Nat.mul 6 w) 6))) (fldW WQ (Nat.mul 21 w) 21)
      (fldW WF (Nat.mul 21 w) 21) 1) = true := by quickRfl

theorem neg_WT : Bool.not (Nat.beq (wordC CFSG.KD.HNPtC.GT (pcF 1)) (WT 0)) = true := by quickRfl
theorem neg_chain : Bool.not (Nat.beq (CFSG.KC.LL.HN.mm (WT 0) (YT 0)) (YT 2)) = true := by
  quickRfl
theorem neg_T4 : Bool.not (ptsImg TX MS CM3 M (trM CFSG.KD.HNPtC.T4) FT FT 40) = true := by
  quickRfl
theorem neg_rep : Bool.not (ptsImg TX MS CM3 M (trM (YT (fldW KP 6 6))) (PF 1) (PF 1) 2) = true :=
  by quickRfl

end CertificateChecks.KernelSporSch.HNPt2086

end
