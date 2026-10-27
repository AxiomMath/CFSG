module

public import Certificates.Kernel.Fi22Core.ChainDefs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22C

set_option Elab.async false

theorem hd_ok : hdK = true := by quickRfl
theorem t34_ok : t34K = true := by quickRfl
theorem u2hd_ok : u2Hd = true := by quickRfl
theorem cover_ok : coverK = true := by quickRfl
theorem sizes_ok : sizesK = true := by quickRfl

end CertificateChecks.KernelFi22C

#kon_slices CertificateChecks.KernelFi22C.t0Sl 0 55
#kon_slices CertificateChecks.KernelFi22C.t1Sl 0 44
#kon_slices CertificateChecks.KernelFi22C.t2Sl 0 27
#kon_slices CertificateChecks.KernelFi22C.u2Sl 0 11

end
