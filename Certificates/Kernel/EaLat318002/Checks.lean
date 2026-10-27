module

public import Certificates.Kernel.EaLat318002.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelEaLat318002

set_option maxRecDepth 100000

#kc_each ch318002e 0 8

#kc_each ch318002u 0 12

theorem ch318002z_ok : ch318002z = true := by quickRfl

#kc_each ch318002g 0 27

end CertificateChecks.KernelEaLat318002

end
