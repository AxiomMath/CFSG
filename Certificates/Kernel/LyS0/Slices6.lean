module

public import Certificates.Kernel.LyS0.Split
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelLyS0.leftCA 18 21

#kc_each CertificateChecks.KernelLyS0.leftCB 18 21

namespace CertificateChecks.KernelLyS0

theorem leftC18 : leftC (nat_lit 18) = true := leftC_of _ leftCA18 leftCB18

theorem leftC19 : leftC (nat_lit 19) = true := leftC_of _ leftCA19 leftCB19

theorem leftC20 : leftC (nat_lit 20) = true := leftC_of _ leftCA20 leftCB20

end CertificateChecks.KernelLyS0

#kc_each CertificateChecks.KernelLyS0.sortC 18 21

end
