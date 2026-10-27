module

public import Certificates.Kernel.W4RowFi22W.Let
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelW4F22

theorem w4f22_let : letK = true := by quickRfl

theorem w4f22_aonly : aOnlyK = true := by quickRfl

end CertificateChecks.KernelW4F22

open CertificateChecks.KernelW4F22

#kc_each CertificateChecks.KernelW4F22 w4f22r relK 0 66

#kc_each CertificateChecks.KernelW4F22 w4f22m movK 0 5

#kc_each CertificateChecks.KernelW4F22 w4f22i invK 0 2

end
