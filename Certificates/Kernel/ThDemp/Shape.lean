module

public import Certificates.Kernel.ThDemp.Data

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

theorem shape_ok : shapeChk dempData = true := by decide +kernel

end CertificateChecks.KernelThDemp

end
