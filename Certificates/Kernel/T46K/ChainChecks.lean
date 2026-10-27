module

public import Certificates.Kernel.T46K.ChainDefs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT46

set_option Elab.async false

theorem hd_ok : hdK = true := by quickRfl
theorem t234_ok : t234K = true := by quickRfl
theorem sizes_ok : sizesK = true := by quickRfl

end CertificateChecks.KernelT46

#kon_slices CertificateChecks.KernelT46.t0Sl 0 11
#kon_slices CertificateChecks.KernelT46.t1Sl 0 8

end
