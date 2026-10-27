module

public import Certificates.Kernel.O8Frame9490.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8F

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelO8
open CFSG.KC.O8F CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

theorem kBindB : allN 3 (fun j => arrEqK 136 8 betaArrs[j]! (J.S j)) = true := by quickRfl

theorem kBindT : allN 4 (fun j => arrEqK 136 8 t0S[j]! (T.S j)) = true := by quickRfl

theorem kBindTau : arrEqK 136 8 tauArr TauK = true := by quickRfl

theorem kBindS : arrEqK 136 8 sArr SK = true := by quickRfl

theorem kGen : [BK 0, BK 1, BK 2, CK, TauK, SK].all (fun x => bAnd(okK x, siftOm x)) = true := by
  quickRfl

theorem kConj : allN 3 (fun g => allN 3 fun i => siftJ (cjM (NGK g) (BK i))) = true := by quickRfl

theorem kRel0 : Nat.beq (cjM CK (BK 0)) (BK 1) = true := by quickRfl

theorem kRel1 : Nat.beq (cjM CK (BK 1)) (BK 2) = true := by quickRfl

theorem kSix : allN 6 (fun k => bAnd(Nat.beq (suppK (sixK k)) 108,
    allN 6 fun l => Nat.beq k l || !(Nat.beq (sixK k) (sixK l)))) = true := by quickRfl

theorem kTR : allN 3 (fun i => bAnd(Nat.beq (rcnt (J.LR i)) 3, allN 3 fun k => cnM (trJ i k))) =
    true := by quickRfl

theorem kWords : candWords.all (fun w => okK (nWK w)) = true := by quickRfl

theorem kZ : okK ZK = true := by quickRfl

theorem kElt : allN 3 (fun a => allN 3 fun b => allN 3 fun c => eltK a b c) = true := by quickRfl

theorem kPsi : (List.range 5).permutations'.all psiOK = true := by quickRfl

theorem kSwap : (!(Nat.beq (psiK [1, 2, 0, 3, 4]) pidM)) = true := by quickRfl

end CertificateChecks.KernelO8F

end
