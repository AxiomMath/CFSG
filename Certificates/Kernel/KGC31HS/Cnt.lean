module

public import Certificates.Kernel.KGC31HS.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31HS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.KGC31P

theorem kC16 : Nat.beq (cbP.countP (pcommAll 100 7 u16P)) 16 = true := by quickRfl

theorem kC8 : Nat.beq (cbP.countP (pcommAll 100 7 u8P)) 64 = true := by quickRfl

theorem kCov : Nat.beq (pcountProducts 100 7 invCovK (trPL 100 7 CT0.LR CT0.TR 2) (pidn 100 7))
    512 = true := by quickRfl

end CertificateChecks.KernelKGC31HS

end
