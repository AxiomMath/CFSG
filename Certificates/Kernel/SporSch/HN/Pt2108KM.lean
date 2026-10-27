module

public import Certificates.Kernel.SporSch.HN.Pt2108Defs
public import Certificates.Kernel.LocalQT.Tc.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2108

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KC.LL.HNXT4 CFSG.KC.LL.HNXSyl CFSG.KS.EnumBase
open CFSG.KD.HNPt2108 CFSG.Sporadic.HNSchreier CFSG.KD.LgHNX

theorem g_ok : bAnd(allN 5 (fun j => Nat.beq (GMf j) (liftM FAData.pLift[j]!)),
    Nat.beq (GMf 5) (wordC CFSG.KD.HNPt.R (FAData.pKernel.map scodeK))) = true := by quickRfl

theorem neg_g : Bool.not (Nat.beq (GMf 1) (liftM FAData.pLift[0]!)) = true := by quickRfl
theorem neg_q : Bool.not (strictB (EM 1) fun e => Nat.beq (CFSG.KC.LL.HN.mm e e)
    CFSG.KD.OrdHN.ONE) = true := by quickRfl
theorem neg_r : Bool.not (strictB (wordC CFSG.KD.HNPt.R ((FAData.wRoot[0]!).map (33 + ·))) fun S =>
    Nat.beq (CFSG.KC.LL.HN.mm (EM 2) S) (CFSG.KC.LL.HN.mm S
      (wordC CFSG.KD.HNPt.R ((FAData.wHWord[0]!).map scodeK)))) = true := by quickRfl
theorem neg_p : Bool.not (ptsFn TX MS CM3 M (trM (GMf 0)) (fun t => f21 OM t)
    (fun t => f21 OM (f14 (SGf 1) t)) 64) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNPt2108

set_option Elab.async false

#kqb_range CertificateChecks.KernelSporSch.HNPt2108.pK CertificateChecks.KernelSporSch.HNPt2108.pS 0 90
#kqb_all CertificateChecks.KernelSporSch.HNPt2108.pK CertificateChecks.KernelSporSch.HNPt2108.pS 90
#kqb_range CertificateChecks.KernelSporSch.HNPt2108.qK CertificateChecks.KernelSporSch.HNPt2108.qS 0 27
#kqb_all CertificateChecks.KernelSporSch.HNPt2108.qK CertificateChecks.KernelSporSch.HNPt2108.qS 27
#kqb_range CertificateChecks.KernelSporSch.HNPt2108.rK CertificateChecks.KernelSporSch.HNPt2108.rS 0 6
#kqb_all CertificateChecks.KernelSporSch.HNPt2108.rK CertificateChecks.KernelSporSch.HNPt2108.rS 6

end
