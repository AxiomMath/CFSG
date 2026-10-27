module

public import Certificates.Kernel.Fi22Reps.Each
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option Elab.async false

public section

namespace CertificateChecks.KernelFi22Reps

theorem ch13621ord_eq : ch13621ord = true := by quickRfl

end CertificateChecks.KernelFi22Reps

#kc_each CertificateChecks.KernelFi22Reps.ch13621xt 0 4

#kc_each CertificateChecks.KernelFi22Reps.ch13621par 0 4

#kc_each CertificateChecks.KernelFi22Reps.ch13621phi 0 4

#kc_each CertificateChecks.KernelFi22Reps.ch13621fix 0 4

#kc_each CertificateChecks.KernelFi22Reps.ch13621levb 0 7

end
