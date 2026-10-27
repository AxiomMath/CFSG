module

public import Certificates.Kernel.TwoHSLe4.NormQ
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTwoHSLe4.NormP

theorem na : chkAN = true := by quickRfl

end CertificateChecks.KernelTwoHSLe4.NormP

end
