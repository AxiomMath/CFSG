module

public import Certificates.Data.E8TenTwo

public section

namespace CertificateChecks.KernelE8TenTwo

theorem ratOk_true : E8TenTwo.ratOk () = true := by decide +kernel

theorem colsOk_true : E8TenTwo.colsOk () = true := by decide +kernel

theorem wordsOk_true : E8TenTwo.wordsOk () = true := by decide +kernel

theorem bfsOk_true : E8TenTwo.bfsOk () = true := by decide +kernel

end CertificateChecks.KernelE8TenTwo

end
