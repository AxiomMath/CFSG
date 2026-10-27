module

public import Certificates.Data.Kernel.PermCent.U33Twin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.GH74.KGroups.U33 CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.U33T

theorem k21200 : invConjC = true := by
  decide +kernel

end CertificateChecks.KernelPermCent
