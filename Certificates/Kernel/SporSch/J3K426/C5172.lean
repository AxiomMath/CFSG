module

public import Certificates.Kernel.SporSch.J3K426.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J3KT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow

theorem c5172 : Nat.beq (pcomp 6156 13 (mask 13) (F 24) (L 4))
    (pcomp 6156 13 (mask 13) (pcomp 6156 13 (mask 13) X1 (L 4)) (F 24)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.J3KT

end
