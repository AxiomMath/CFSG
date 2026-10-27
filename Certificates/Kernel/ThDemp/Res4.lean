module

public import Certificates.Kernel.ThDemp.Data

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

theorem res4_ok : resChk dempData 4 = true := by decide +kernel

end CertificateChecks.KernelThDemp

end
