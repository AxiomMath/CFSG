module

public import Certificates.Kernel.Stroth77.SplitData
public import Certificates.Data.Kernel.Stroth77.SplitW4
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSplit778711

open CFSG.KC.Stroth77SP

theorem ch778711_w4 : w4OK tabs = true := by quickRfl

end CertificateChecks.KernelSplit778711
