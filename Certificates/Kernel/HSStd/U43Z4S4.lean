module

public import Certificates.Kernel.HSStd.U43Z4Pt
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.U43Z4

theorem ksC2 : ksC (nat_lit 2) = true := (ksC_eq_ksCPt (nat_lit 2)).trans (by quickRfl)

theorem ksC3 : ksC (nat_lit 3) = true := (ksC_eq_ksCPt (nat_lit 3)).trans (by quickRfl)

end CertificateChecks.KernelHSStd.U43Z4

end
