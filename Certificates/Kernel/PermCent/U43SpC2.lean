module

public import Certificates.Kernel.PermCent.U43SpP

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

theorem sp_coset2 : spCoset 2 = true := by decide +kernel

end CertificateChecks.KernelPermCent.U43Quat

end
