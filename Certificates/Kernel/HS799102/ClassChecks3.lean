module

public import Certificates.Kernel.HS799102.ClassData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent

theorem ch799102_c3 : classK 100 7 pG pGI 4 (TH.F 4) R3 = true := by quickRfl

end CertificateChecks.KernelHS799102

end
