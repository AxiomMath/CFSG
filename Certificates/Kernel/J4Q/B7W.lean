module

public import Certificates.Kernel.J4Q.B7K
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q

#j4q_all CFSG.KD.J4Q.BW CertificateChecks.KernelJ4Q.b7WitK 221

theorem b7Base_chk : allR 15 (fun i => b7BaseK (Nat.succ i)) = true := by quickRfl

end CertificateChecks.KernelJ4Q

end
