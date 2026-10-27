module

public import Certificates.Kernel.EaLat10506.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelEaLat10506

set_option maxRecDepth 100000

#kc_each ch10506e 0 8

#kc_each ch10506u 0 12

theorem ch10506z_ok : ch10506z = true := by quickRfl

#kc_each ch10506g 0 27

end CertificateChecks.KernelEaLat10506

end
