module

public import Certificates.Kernel.Fi22Alt.Defs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelFi22Alt.altSl 0 71

namespace CertificateChecks.KernelFi22Alt

theorem mv_ok : altMv = true := by quickRfl

end CertificateChecks.KernelFi22Alt

end
