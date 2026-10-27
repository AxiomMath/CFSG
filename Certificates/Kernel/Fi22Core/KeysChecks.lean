module

public import Certificates.Kernel.Fi22Core.Keys
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22C

set_option Elab.async false

theorem root_ok : rootK = true := by quickRfl

end CertificateChecks.KernelFi22C

#kon_slices CertificateChecks.KernelFi22C.sortSl 0 10

end
