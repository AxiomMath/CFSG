module

public import Certificates.Kernel.ThDemp.Data

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

theorem res2_ok : resChk dempData 2 = true := by decide +kernel

end CertificateChecks.KernelThDemp

end
