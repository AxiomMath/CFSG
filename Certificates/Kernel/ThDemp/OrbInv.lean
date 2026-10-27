module

public import Certificates.Kernel.ThDemp.OrbData

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

theorem inv_ok : invChk dempData orbData = true := by decide +kernel

end CertificateChecks.KernelThDemp

end
