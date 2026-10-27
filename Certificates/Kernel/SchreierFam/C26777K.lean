module

public import Certificates.Kernel.Sporadic.OddCore.HN2089K
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.F4Side

open CFSG.EvenSporadicStandard.HNRecog.SideF4 CFSG.KC.Enum CFSG.KS CFSG.KS.Prim
  CertificateChecks.KernelSpor CertificateChecks.KernelSpor.HN2089

theorem wqJ : allN 8 (fun i => wordEqK 800 10 (mask 10) (pidn 800 10) HQS siP 11 qWordsJ[i]!
    (HQQ i)) = true := by
  decide +kernel

theorem weE : allN 5 (fun i => wordEqK 800 10 (mask 10) (pidn 800 10) HQS siP 11 eWords[i]!
    (HQB eMasks[i]!)) = true ∧
    wordEqK 800 10 (mask 10) (pidn 800 10) HQS siP 11 bWord (HQB bMask) = true := by
  constructor <;> decide +kernel

end CertificateChecks.KernelSchreierFam.F4Side
