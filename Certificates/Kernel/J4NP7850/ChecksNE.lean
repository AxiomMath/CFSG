module

public import Certificates.Kernel.J4NP7850.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelJ4NP7850

theorem c7850_ne : ((S5L.all fun ch => !ch.isEmpty) && S6L.all fun ch => !ch.isEmpty) = true := by
  quickRfl

end CertificateChecks.KernelJ4NP7850

end
