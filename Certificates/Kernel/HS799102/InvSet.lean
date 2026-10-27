module

public import Certificates.Kernel.HS799102.InvData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent

theorem ch799102_isr : setOrbK 100 7 hG 3 SM SR = true := by quickRfl

end CertificateChecks.KernelHS799102

end
