
module

import Certificates.Kernel.MonsterB.Ind3034.Checks
import CFSG.Certificates.Kernel.Common.Harness

namespace CFSG.KC.Ind3034.Neg

open CertificateChecks.KernelMonB CFSG.KLie.CT

example : notB (chkX fun g => IG.F g ^^^ 1) = true := by quickRfl

example : notB (chkW fun g => IG.F g ^^^ (1 <<< (12 * 1045))) = true := by quickRfl

example : notB (chkT fun t => ITr.F t ^^^ (1 <<< (12 * 3509))) = true := by quickRfl

example : notB (chkS fun t => ITr.F t ^^^ (1 <<< (12 * 3478))) = true := by quickRfl

example : notB (zFrom IG.F (SortTree.recT CertificateChecks.Diag3031.R 6 292)
    (CFSG.KD.I3034.W.c0.set 0 (CFSG.KD.I3034.W.c0[0]! + 1)) 0) = true := by quickRfl

example : notB (zFrom IG.F (SortTree.recT CertificateChecks.Diag3031.R 6 292)
    (CFSG.KD.I3034.W.c0.set 0 5760) 0) = true := by quickRfl

example : notB (zFrom IG.F (SortTree.recT CertificateChecks.Diag3031.R 6 292)
    CFSG.KD.I3034.W.c0.dropLast 0) = true := by quickRfl

example : notB (zFrom (fun g => IG.F g ^^^ (1 <<< (12 * 1047)))
    (SortTree.recT CertificateChecks.Diag3031.R 6 292) CFSG.KD.I3034.W.c0 0) = true := by quickRfl

end CFSG.KC.Ind3034.Neg
