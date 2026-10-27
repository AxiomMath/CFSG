module

public import Certificates.Data.Kernel.PermCent.M11BTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.M11B

theorem k260380 : o4C = true := by decide +kernel

end CertificateChecks.KernelPermCent
