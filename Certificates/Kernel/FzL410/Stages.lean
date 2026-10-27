module

public import Certificates.Data.Kernel.FzL410.Codes
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.FzL410K

open Certificates.FzL410.K

theorem normInj_true : normInjB = true := by quickRfl

theorem stageA_true : stageAB = true := by quickRfl

theorem stageB_true : stageBB = true := by quickRfl

end CertificateChecks.FzL410K

end
