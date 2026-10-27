module

public import Certificates.Data.Kernel.EvenBN.YamadaK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27030

open CFSG.KC.YamadaK

theorem k0 : c3101 0 = true := by quickRfl
theorem k1 : c3101 1 = true := by quickRfl
theorem k2 : c3101 2 = true := by quickRfl
theorem k3 : c3101 3 = true := by quickRfl

end CertificateChecks.Batch27030

end
