module

public import Certificates.Kernel.HSStd.U43Z4Pt
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.U43Z4

theorem ksC0 : ksC (nat_lit 0) = true := (ksC_eq_ksCPt (nat_lit 0)).trans (by quickRfl)

theorem ksC1 : ksC (nat_lit 1) = true := (ksC_eq_ksCPt (nat_lit 1)).trans (by quickRfl)

end CertificateChecks.KernelHSStd.U43Z4

end
