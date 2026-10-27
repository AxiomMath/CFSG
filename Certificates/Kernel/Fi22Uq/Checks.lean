module

public import Certificates.Kernel.Fi22Uq.Defs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Uq

set_option Elab.async false

theorem c25230leaf_ok : c25230leaf = true := by quickRfl
theorem c25230dist_ok : c25230dist = true := by quickRfl
theorem c25230comm_ok : c25230comm = true := by quickRfl
theorem c25230phi_ok : c25230phi = true := by quickRfl

end CertificateChecks.KernelFi22Uq

#kon_slices CertificateChecks.KernelFi22Uq.c25230act0 0 16
#kon_slices CertificateChecks.KernelFi22Uq.c25230act1 0 2

end
