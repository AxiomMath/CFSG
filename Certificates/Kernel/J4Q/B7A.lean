module

public import Certificates.Kernel.J4Q.B7K
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

#j4q_all CFSG.KD.J4Q.BF5 CertificateChecks.KernelJ4Q.b7Fix5 15

#j4q_all CFSG.KD.J4Q.BF6 CertificateChecks.KernelJ4Q.b7Fix6 28

theorem b7Lit_chk : b7LitOK = true := by quickRfl

theorem b7Roots_chk : b7Roots = true := by quickRfl

theorem b7V_chk : b7VK = true := by quickRfl

theorem b7Cross_chk : b7CrossOK = true := by quickRfl

end CertificateChecks.KernelJ4Q

end
