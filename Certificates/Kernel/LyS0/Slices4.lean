module

public import Certificates.Kernel.LyS0.Split
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelLyS0.leftCA 12 15

#kc_each CertificateChecks.KernelLyS0.leftCB 12 15

namespace CertificateChecks.KernelLyS0

theorem leftC12 : leftC (nat_lit 12) = true := leftC_of _ leftCA12 leftCB12

theorem leftC13 : leftC (nat_lit 13) = true := leftC_of _ leftCA13 leftCB13

theorem leftC14 : leftC (nat_lit 14) = true := leftC_of _ leftCA14 leftCB14

end CertificateChecks.KernelLyS0

#kc_each CertificateChecks.KernelLyS0.sortC 12 15

end
