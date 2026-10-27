module

public import Certificates.Kernel.J4Q.VlBase
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

@[expose] noncomputable def vlJ1 (q : Nat) : Bool := vlJK (Nat.add 38 q)

#j4q_all CFSG.KD.J4Q.VLJ1 CertificateChecks.KernelJ4Q.vlJ1 37

end CertificateChecks.KernelJ4Q

end
