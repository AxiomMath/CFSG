module

public import Certificates.Kernel.LyS0.Split
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelLyS0.leftCA 21 24

#kc_each CertificateChecks.KernelLyS0.leftCB 21 24

namespace CertificateChecks.KernelLyS0

theorem leftC21 : leftC (nat_lit 21) = true := leftC_of _ leftCA21 leftCB21

theorem leftC22 : leftC (nat_lit 22) = true := leftC_of _ leftCA22 leftCB22

theorem leftC23 : leftC (nat_lit 23) = true := leftC_of _ leftCA23 leftCB23

end CertificateChecks.KernelLyS0

#kc_each CertificateChecks.KernelLyS0.sortC 21 24

end
