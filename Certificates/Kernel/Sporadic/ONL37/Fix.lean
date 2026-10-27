module

public import Certificates.Kernel.Sporadic.ONL37.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONL37

set_option Elab.async false

theorem l37Fix_ok : l37Fix = true := by quickRfl

end CertificateChecks.KernelSpor.ONL37

end
