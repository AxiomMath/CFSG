module

public import Certificates.Kernel.Fi22Nfp.Defs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22N

set_option Elab.async false

theorem hd_ok : hdN = true := by quickRfl
theorem small_ok : smallK = true := by quickRfl
theorem sizes_ok : sizesN = true := by quickRfl
theorem uInv_ok : uInvK = true := by quickRfl
theorem uBase_ok : uBaseK = true := by quickRfl
theorem uSift_ok : uSiftK = true := by quickRfl

end CertificateChecks.KernelFi22N

#kon_slices CertificateChecks.KernelFi22N.t6Sl 0 14
#kon_slices CertificateChecks.KernelFi22N.candN 1 6
#kon_slices CertificateChecks.KernelFi22N.uConj 0 6
#kon_slices CertificateChecks.KernelFi22N.uRecSl 0 14
#kon_slices CertificateChecks.KernelFi22N.nfpSl 0 128

end
