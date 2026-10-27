module

public import Certificates.Kernel.SporSch.PairHS.Chain
public import Certificates.Data.Kernel.SporSch.PairK
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.PHSWO

open CFSG.KS.SporSch CertificateChecks.KernelSporSch

theorem o10 : ordWK 3850 12 CFSG.Sporadic.Schreier.PairHS.bs [PHSC.S 1, PHSC.S 1, PHSC.S 0] 10 =
    true := by
  quickRfl

theorem o5Neg : (ordWK 3850 12 CFSG.Sporadic.Schreier.PairHS.bs [PHSC.S 1, PHSC.S 1, PHSC.S 0]
    5).not = true := by
  quickRfl

end CertificateChecks.KernelSporSch.PHSWO

end
