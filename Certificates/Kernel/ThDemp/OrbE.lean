module

public import Certificates.Kernel.ThDemp.OrbData

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

theorem codes_ok : codesChk dempData orbData = true := by decide +kernel

theorem elt1_ok : eltChk1 dempData orbData = true := by decide +kernel

theorem cent_ok : centChk dempData orbData = true := by decide +kernel

theorem q_ok : qChk dempData orbData = true := by decide +kernel

theorem norm_ok : normChk dempData orbData = true := by decide +kernel

end CertificateChecks.KernelThDemp

end
