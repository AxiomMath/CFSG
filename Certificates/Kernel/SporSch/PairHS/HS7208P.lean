module

public import Certificates.Kernel.SporSch.PairHS.HS7208Fns
public import Certificates.Kernel.SporSch.PairJ3.GenClT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HS78

theorem t0_ok : tB = true := by quickRfl
theorem small_ok : smallB = true := by quickRfl

end CertificateChecks.KernelSporSch.HS78

#kss_b2 CertificateChecks.KernelSporSch.HS78 CertificateChecks.KernelSporSch.HS78.pB 0 8 9
#kss_b2all CertificateChecks.KernelSporSch.HS78 CertificateChecks.KernelSporSch.HS78.pB 8 9

end
