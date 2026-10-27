module

public import Certificates.Kernel.TwoDFix.Glue

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTwoDFix

theorem betaK_ok : betaK = true := by decide +kernel

end CertificateChecks.KernelTwoDFix

end
