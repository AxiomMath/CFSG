module

public import Certificates.Data.Kernel.PermCent.Sp6E4QuatTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.Sp6E

theorem k124i1 : p124i1 = true := by decide +kernel

end CertificateChecks.KernelPermCent
