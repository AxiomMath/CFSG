module

public import Certificates.Kernel.ThDemp.Data

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

theorem res5_ok : resChk dempData 5 = true := by decide +kernel

end CertificateChecks.KernelThDemp

end
