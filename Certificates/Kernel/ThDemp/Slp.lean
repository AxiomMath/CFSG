module

public import Certificates.Kernel.ThDemp.Data

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

theorem slp_ok : slpChk dempData = true := by decide +kernel

end CertificateChecks.KernelThDemp

end
