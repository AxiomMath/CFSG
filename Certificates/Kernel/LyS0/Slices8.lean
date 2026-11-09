module

public import Certificates.Kernel.LyS0.Split
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelLyS0.leftCA 24 27

#kc_each CertificateChecks.KernelLyS0.leftCB 24 27

namespace CertificateChecks.KernelLyS0

theorem leftC24 : leftC (nat_lit 24) = true := leftC_of _ leftCA24 leftCB24

theorem leftC25 : leftC (nat_lit 25) = true := leftC_of _ leftCA25 leftCB25

theorem leftC26 : leftC (nat_lit 26) = true := leftC_of _ leftCA26 leftCB26

end CertificateChecks.KernelLyS0

#kc_each CertificateChecks.KernelLyS0.sortC 24 27

end
