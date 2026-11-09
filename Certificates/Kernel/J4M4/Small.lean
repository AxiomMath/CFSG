module

public import Certificates.Kernel.J4M4.DefsK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M4

theorem smallKK_ok : smallKK = true := by quickRfl

theorem small_k : smallK = true := smallK_eq.trans smallKK_ok

theorem bound_k : boundK = true := by decide +kernel

theorem sq_k : sqK = true := by decide +kernel

end CertificateChecks.KernelJ4M4
