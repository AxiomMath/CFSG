module

public import Certificates.Kernel.J4M4.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M4

theorem small_k : smallK = true := by decide +kernel

theorem bound_k : boundK = true := by decide +kernel

theorem sq_k : sqK = true := by decide +kernel

end CertificateChecks.KernelJ4M4
