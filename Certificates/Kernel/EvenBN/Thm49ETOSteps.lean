module

public import Certificates.Kernel.EvenBN.Thm49ETOData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT49

open CFSG.KC.Enum CFSG.KS CFSG.KD.T49

theorem steps43 : checkSteps w43 p43 = true := by quickRfl

end CertificateChecks.KernelT49

end
