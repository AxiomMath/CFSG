module

public import Certificates.Kernel.Sporadic.OddCore.J3TabK
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinE
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSpor.J3Tab

theorem pin_ok : CFSG.EvenSporadicStandard.Fin76b.TablePin.pinCheck 128 mF tI = true := by
  quickRfl

end CertificateChecks.KernelSpor.J3Tab

end
