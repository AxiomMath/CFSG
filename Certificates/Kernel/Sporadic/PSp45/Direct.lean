module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.GH74.KGroups.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.PSp45

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Sporadic.Schreier CFSG.GH74.KGroups

theorem tauSift : (List.finRange 45).all (fun j => QP45.sift (tauPerm j) 0) = true := by
  quickRfl

theorem xyFacts : (orderIs x45 2 && orderIs y45 5 && pairInvB ws45 x45 y45) = true := by
  quickRfl

theorem normOK : normCheck QP45 QA45.original.toList x45 y45 = true := by quickRfl

end CertificateChecks.KernelSpor.PSp45

end
