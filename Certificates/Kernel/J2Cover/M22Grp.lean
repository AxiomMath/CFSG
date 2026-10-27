module

public import Certificates.Kernel.J2Cover.M22Fold
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Models
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models

theorem cocyC : cocycleCheck = true := by
  rw [cocycleCheck_eq, mt_eq, lm_eq, fR_eq, hR_eq]
  unfold cocycleCheckG normCocOKG treeNormOKG
  simp only [allLt_eq_allN]
  quickRfl

theorem grpC : groupCheck = true := by
  rw [groupCheck_eq, mt_eq, bt_eq, fR_eq]
  unfold groupCheckG centerOK rootCounts sqCount fourthCount
  simp only [allLt_eq_allN, countFold_eq]
  quickRfl

end CertificateChecks.KernelJ2Cover

end
