module

public import Certificates.Kernel.ThDemp.OrbData

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

theorem orb_ok : orbChk dempData orbData = true := by decide +kernel

end CertificateChecks.KernelThDemp

end
