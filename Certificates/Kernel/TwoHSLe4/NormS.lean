module

public import Certificates.Kernel.TwoHSLe4.NormD
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelTwoHSLe4.Norm

open CFSG.EvenSporadicStandard.TwoHS

theorem sv_ok : nvL.all (fun b => !(nvL.any fun b' => (rmul b b').mod2 == R4.one) || svL.contains b) =
    true := by
  quickRfl

end CertificateChecks.KernelTwoHSLe4.Norm

end
