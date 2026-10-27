module

public import Certificates.Kernel.Seitz.B45
public import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelSeitz.statsK 0 15
#kc_each CertificateChecks.KernelSeitz.admK 0 16

namespace CertificateChecks.KernelSeitz

open CFSG.KC.SeitzB45

theorem k_cover : coverOKF mtT 15 P6.SL = true := by decide +kernel

end CertificateChecks.KernelSeitz

end
