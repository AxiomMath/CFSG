module

public import Certificates.Kernel.Fi22Cls.Each
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option Elab.async false

public section

namespace CertificateChecks.KernelFi22Cls

theorem ch13620gen_eq : ch13620gen = true := by quickRfl

end CertificateChecks.KernelFi22Cls

#kc_each CertificateChecks.KernelFi22Cls.ch13620rep 0 4

#kc_each CertificateChecks.KernelFi22Cls.ch13620clos 0 4

#kc_each CertificateChecks.KernelFi22Cls.ch13620orb 0 9

end
