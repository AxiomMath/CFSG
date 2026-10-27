module

public import Certificates.Kernel.G24Th799103.InvData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

open CFSG.KC.PCent

theorem ch799103_isr : setOrbK 1365 11 hG 3 DM SR = true := by quickRfl

theorem ch799103_isf : setOrbK 1365 11 kG 3 EM SF = true := by quickRfl

end CertificateChecks.KernelG24Th

end
