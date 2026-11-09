module

public import Certificates.Kernel.ThDemp.Data

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

theorem res0_ok : resChkR dempData 0 0 2 = true := by decide +kernel

end CertificateChecks.KernelThDemp

end
