module

public import Certificates.Kernel.ThDemp.Data

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

theorem res0_ok : resChk dempData 0 = true := by decide +kernel

end CertificateChecks.KernelThDemp

end
