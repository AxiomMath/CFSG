module

public import Certificates.Kernel.J4Q.VcK
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q

#j4q_all CFSG.KD.J4Q.VNM CertificateChecks.KernelJ4Q.nmK 10

#j4q_all CFSG.KD.J4Q.VA9C CertificateChecks.KernelJ4Q.ngA9OK 4

#j4q_all CFSG.KD.J4Q.VB7C CertificateChecks.KernelJ4Q.ngB7OK 4

#j4q_all CFSG.KD.J4Q.VXI CertificateChecks.KernelJ4Q.ngXiOK 4

theorem ngMask_chk : ngMaskOK = true := by quickRfl

theorem ngB3_chk : ngB3OK = true := by quickRfl

theorem il17_chk : allR 272 (fun i => Nat.blt (getN 0 IL17 i) 2048) = true := by quickRfl

end CertificateChecks.KernelJ4Q

end
