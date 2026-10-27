module

public import Certificates.Kernel.Om1K.BDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm1.B

open CFSG.KC.Enum CFSG.KC.BfsPin

theorem kOrb : allN 576 (oNodeOK BD.OP) = true := by quickRfl

theorem kOS : distinctK 576 tupK BD.OS = true := by quickRfl

end CertificateChecks.KernelOm1.B

end
