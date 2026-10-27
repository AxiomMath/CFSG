module

public import Certificates.Kernel.PermCent.U43QuatP

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

theorem cfg_coset4 : cfgCoset 4 = true := by decide +kernel

end CertificateChecks.KernelPermCent.U43Quat

end
