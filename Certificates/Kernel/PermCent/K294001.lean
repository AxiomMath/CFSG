module

public import Certificates.Data.Kernel.PermCent.Sp6E4Twin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.Sp6E
  CFSG.Certificates.Kernel.PkCV.Sp6B

theorem k294001 : tC = true := by decide +kernel

end CertificateChecks.KernelPermCent
