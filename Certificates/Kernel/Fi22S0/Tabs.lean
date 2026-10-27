module

public import Certificates.Kernel.Fi22S0.Each
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option Elab.async false

public section

namespace CertificateChecks.KernelFi22S0

theorem ch131101base_eq : ch131101base = true := by quickRfl

end CertificateChecks.KernelFi22S0

#kc_each CertificateChecks.KernelFi22S0.ch131101tree 0 9

#kc_each CertificateChecks.KernelFi22S0.ch131101left 0 9

#kc_each CertificateChecks.KernelFi22S0.ch131101sort 0 9

end
