module

public import Certificates.Kernel.Sporadic.ONC.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONC

set_option Elab.async false

theorem misc_ok : miscOK = true := by quickRfl

end CertificateChecks.KernelSpor.ONC

end
