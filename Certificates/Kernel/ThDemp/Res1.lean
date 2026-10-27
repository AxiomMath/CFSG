module

public import Certificates.Kernel.ThDemp.Data

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

theorem res1_ok : resChk dempData 1 = true := by decide +kernel

end CertificateChecks.KernelThDemp

end
