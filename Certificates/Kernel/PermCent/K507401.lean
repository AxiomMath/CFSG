module

public import Certificates.Data.Kernel.PermCent.Sp6BTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.Sp6B

theorem k507401 : twinLayC = true := by decide +kernel

end CertificateChecks.KernelPermCent
