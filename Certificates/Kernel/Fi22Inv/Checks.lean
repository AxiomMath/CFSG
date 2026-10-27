module

public import Certificates.Kernel.Fi22Inv.Defs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22I

set_option Elab.async false

theorem stab_ok : stabK = true := by quickRfl
theorem att_ok : attAllK = true := by quickRfl

end CertificateChecks.KernelFi22I

#kon_slices CertificateChecks.KernelFi22I.repSl 0 27
#kon_slices CertificateChecks.KernelFi22I.fixSl 0 128

end
