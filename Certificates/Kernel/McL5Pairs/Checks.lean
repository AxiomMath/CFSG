module

public import Certificates.Kernel.MaxD2.McLP.Enum
public import Certificates.Kernel.MaxD2.McLP.Data
public import Certificates.Kernel.McL5Pairs.Data
public import Certificates.Kernel.McL5Pairs.Chain
public import Certificates.Data.Kernel.McL5Pairs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMcL5Pairs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.McL5P Certificates.McLFivePairs
open CertificateChecks.KernelMaxD2.McLP

theorem k_rgi : allN 2 (fun j => perm275 (RE.G j) (RGI j)) = true := by quickRfl
theorem k_b0 : allN 4 (fun l => Nat.beq (B0 l) (l4 (RE.G 0) (RE.G 1)
    (cj (REP 95) (REPI 95) (RE.G 0)) (cj (REP 95) (REPI 95) (RE.G 1)) l)) = true := by quickRfl
theorem k_b0i : allN 4 (fun l => perm275 (B0 l) (B0I l)) = true := by quickRfl
theorem k_h : allN 3 (fun k => bAnd(wEq NE.G NGI 4 (conjWords[k]!) (HK k), perm275 (HK k) (HKI k))) =
    true := by quickRfl
theorem k_blk : blkK HK HKI B0 BK BKI = true := by quickRfl

theorem k_pw0 : pairWordsP0.all (pairK1 (GP 0) (GP 1) (RE.G 0) (RE.G 1) (RGI 0) (RGI 1) REP REPI) =
    true := by quickRfl
theorem k_pw1 : pairWordsP1.all (pairK1 (GP 0) (GP 1) (RE.G 0) (RE.G 1) (RGI 0) (RGI 1) REP REPI) =
    true := by quickRfl
theorem k_pw2 : pairWordsP2.all (pairK1 (GP 0) (GP 1) (RE.G 0) (RE.G 1) (RGI 0) (RGI 1) REP REPI) =
    true := by quickRfl
theorem k_pw3 : pairWordsP3.all (pairK1 (GP 0) (GP 1) (RE.G 0) (RE.G 1) (RGI 0) (RGI 1) REP REPI) =
    true := by quickRfl
theorem k_pw4 : pairWordsP4.all (pairK1 (GP 0) (GP 1) (RE.G 0) (RE.G 1) (RGI 0) (RGI 1) REP REPI) =
    true := by quickRfl
theorem k_pw5 : pairWordsP5.all (pairK1 (GP 0) (GP 1) (RE.G 0) (RE.G 1) (RGI 0) (RGI 1) REP REPI) =
    true := by quickRfl
theorem k_pw6 : pairWordsP6.all (pairK1 (GP 0) (GP 1) (RE.G 0) (RE.G 1) (RGI 0) (RGI 1) REP REPI) =
    true := by quickRfl

theorem k_act0 : actWordsP0.all (actK NE.G NGI BK BKI) = true := by quickRfl
theorem k_act1 : actWordsP1.all (actK NE.G NGI BK BKI) = true := by quickRfl
theorem k_join : joinWords.all (joinK (GP 0) (GP 1) BK BKI) = true := by quickRfl

theorem k_sgs : allN 8 (fun j => wEq B0 B0I 4 (sgsWords[j]!) (CH.S j)) = true := by quickRfl
theorem k_chp : allN 8 (fun j => perm275 (CH.S j) (CH.SI j)) = true := by quickRfl
theorem k_orb0 : Nat.beq (rcnt (CH.LR 0)) 175 = true := by quickRfl
theorem k_orb1 : Nat.beq (rcnt (CH.LR 1)) 72 = true := by quickRfl
theorem k_orb2 : Nat.beq (rcnt (CH.LR 2)) 10 = true := by quickRfl

end CertificateChecks.KernelMcL5Pairs

end
