module

public import Certificates.Data.Kernel.EvenBN.YamadaK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27031

open CFSG.KC.YamadaK

theorem k0 : c39 0 = true := by quickRfl
theorem k1 : c39 1 = true := by quickRfl
theorem k2 : c39 2 = true := by quickRfl
theorem k3 : c39 3 = true := by quickRfl

end CertificateChecks.Batch27031

end
