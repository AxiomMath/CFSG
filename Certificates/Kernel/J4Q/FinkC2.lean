module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkData
public import Certificates.Kernel.J4Q.Orbits
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.ComponentClassification.RankTwoSporadic.J4Fink

theorem finkC2 : chkFinkC2 = true := by
  unfold chkFinkC2
  rw [tMasks_eq, zMasks_eq]
  quickRfl

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.J4Fink in
theorem c15040 : chkFinkC2 = true := finkC2

end CertificateChecks.KernelJ4Q

end
