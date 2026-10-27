module

public import Certificates.Kernel.Sporadic.Co2Inv.Data
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Inv

open CFSG.KC.Co2InvS

theorem recs9 : ∀ t < 16384, recOK E.CF G YT FW 262144 (Nat.add 147456 t) = true := by
  kc_cover 64

end CertificateChecks.KernelSpor.Co2Inv

end
