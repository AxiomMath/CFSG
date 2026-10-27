module

public import Certificates.Data.Kernel.J4Cent3
public import Certificates.Kernel.J4Count.FixCEData
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Data
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Data.Fin.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.Cent3

open CFSG.KC.J4Cent3 CFSG.KC.J4Five CFSG.KC.J4Q CFSG.KD.J4FixCE
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs

theorem ce_tab : starTabOK PC starMasks ZE = true := by quickRfl

theorem ce_fix : fixOK ZE FL3 = true := by quickRfl

theorem ce_oct : oct6OK GB GP ZE FL3 TL3 = true := by quickRfl

theorem ce_crd : crd16OK ZE CRD3 (FL3 ++ TL3) = true := by quickRfl

theorem ce_dist : distB (FL3 ++ TL3) = true := by quickRfl

theorem ce_cand : Nat.beq (cand3N GB GP ZE CRD3 FL3 TL3) 1 = true := by quickRfl

theorem neg_cand : notB (Nat.beq (cand3N GB GP ZE CRD3 FL3 TL3) 2) = true := by quickRfl

theorem neg_tab : notB (starTabOK PC starMasks
    [1, 0, 11, 2, 19, 5, 21, 13, 7, 4, 23, 3, 20, 8, 10, 15, 6, 17, 12, 9, 18, 16, 22, 14]) = true := by
  quickRfl

theorem neg_fix : notB (fixOK ZE [0, 1, 5, 15, 17]) = true := by quickRfl

theorem neg_oct : notB (oct6OK GB GP ZE FL3 [6, 4, 7, 2, 12, 10]) = true := by quickRfl

theorem neg_crd : notB (crd16OK ZE CRD3 (FL3 ++ [4, 6, 7, 2, 10, 12])) = true := by quickRfl

theorem neg_dist : notB (distB (FL3 ++ [4, 6, 7, 2, 12, 0])) = true := by quickRfl

end CertificateChecks.KernelJ4Count.Cent3

end
