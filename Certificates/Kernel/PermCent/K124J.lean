module

public import Certificates.Data.Kernel.PermCent.Sp6E4QuatTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.Sp6E
  CFSG.EvenSmallLie.Sp6

theorem k124i2 : p124i2 = true := by decide +kernel

theorem k124i3 : p124i3 = true := by decide +kernel

theorem k124i4 : p124i4 = true := by decide +kernel

end CertificateChecks.KernelPermCent
