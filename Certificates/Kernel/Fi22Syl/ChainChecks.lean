module

public import Certificates.Kernel.Fi22Syl.ChainDefs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22S

set_option Elab.async false

theorem hd_ok : hdK = true := by quickRfl
theorem sizes_ok : sizesK = true := by quickRfl
theorem inv_ok : invSK = true := by quickRfl
theorem t1_ok : t1K = true := by quickRfl
theorem sch1_ok : sch1K = true := by quickRfl
theorem term_ok : termSK = true := by quickRfl

end CertificateChecks.KernelFi22S

#kon_slices CertificateChecks.KernelFi22S.swS 0 11
#kon_slices CertificateChecks.KernelFi22S.t0Sl 0 16
#kon_slices CertificateChecks.KernelFi22S.sch0Sl 0 64

end
