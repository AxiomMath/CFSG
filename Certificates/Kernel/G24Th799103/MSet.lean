module

public import Certificates.Kernel.G24Th799103.MData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

open CFSG.KC.PCent

theorem ch799103_mst : setOrbK 1365 11 aG 3 TM ST = true := by quickRfl

end CertificateChecks.KernelG24Th

end
