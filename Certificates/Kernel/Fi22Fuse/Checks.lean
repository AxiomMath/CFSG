module

public import Certificates.Kernel.Fi22Fuse.ChkDefs
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Fuse

theorem c25240flag_ok : c25240flagK = true := by decide +kernel

theorem c25240ev0_ok : c25240ev0 = true := by decide +kernel

end CertificateChecks.KernelFi22Fuse

#kon_slices CertificateChecks.KernelFi22Fuse.c25240evSl 0 10

#kon_slices CertificateChecks.KernelFi22Fuse.c25240Sl 0 128

end
