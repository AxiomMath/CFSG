module

public import Certificates.Kernel.Sporadic.ONPrim.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPrim

theorem prTot_ok : prTot = true := by quickRfl

theorem prHead_ok : prHead = true := by quickRfl

end CertificateChecks.KernelSpor.ONPrim

end
