module

public import Certificates.Data.Kernel.PermCent.A6BTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.GH74.KGroups.A6 CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.A6B

theorem k5159 : a6C = true := by decide +kernel

end CertificateChecks.KernelPermCent
