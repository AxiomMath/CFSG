module

public import Certificates.Kernel.HSStd.U43VbData
public import Certificates.Data.Kernel.U43Case
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelHSStd.U43Vb

open CFSG.KC.U43Case CertificateChecks.KernelHSStd

theorem kSol : solK 820 10 (VbP 0) (VbP 1) VbY.cnt VbY.T 12 = true := by quickRfl

end CertificateChecks.KernelHSStd.U43Vb

end
