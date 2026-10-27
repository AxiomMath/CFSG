module

public import Certificates.Kernel.TwoDFix.Glue

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTwoDFix

theorem qK_ok : qK = true := by decide +kernel

end CertificateChecks.KernelTwoDFix

end
