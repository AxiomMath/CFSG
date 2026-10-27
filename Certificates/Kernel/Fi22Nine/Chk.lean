module

public import Certificates.Kernel.Fi22Nine.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22Nine

theorem elem : elemK = true := by quickRfl

theorem orb : orbK = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22Nine

end
