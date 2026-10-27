module

public import Certificates.Kernel.J4.Data
public import Certificates.Data.Kernel.J4MFix

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN

theorem mfix_ok : j4MFix kd md = true := by quickRfl

end CertificateChecks.KernelBounds.J4

end
