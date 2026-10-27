module

public import Certificates.Kernel.J4Pent.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Pent

open CFSG.KC.J4Pent CFSG.KD.J4Pent

theorem e_ok : Nat.beq (Nat.land eFlags (Nat.xor ONES (maskOf DL))) 0 = true := by quickRfl

end CertificateChecks.KernelJ4Pent

end
