module

public import Certificates.Kernel.ThDemp.Data

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

theorem res3_ok : resChk dempData 3 = true := by decide +kernel

end CertificateChecks.KernelThDemp

end
