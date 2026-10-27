module

public import Certificates.Kernel.J4Q.VlK
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

@[expose] noncomputable def seg1 (q : Nat) : Bool := segK (Nat.add 64 q)

#j4q_all CFSG.KD.J4Q.VSG1 CertificateChecks.KernelJ4Q.seg1 64

end CertificateChecks.KernelJ4Q

end
