module

public import Certificates.Kernel.KGC31M24.Defs7217
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.KGC31M24.Data7217

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.KGC31P
open CFSG.Quasithin.KGC31.M24 CertificateChecks.KernelSporSch

theorem kLq : Nat.beq (pcountProducts 24 5 (pcommAll 24 5 u5P) (trPL 24 5 CLQ.LR CLQ.TR 5)
    (pidn 24 5)) 64 = true := by quickRfl

theorem kLs : Nat.beq (pcountProducts 24 5 (pfixesBlocks 5 tets) (trPL 24 5 CLS.LR CLS.TR 5)
    (pidn 24 5)) 192 = true := by quickRfl

theorem kC2 : (Nat.beq (cb0P.countP (pcommAll 24 5 oP)) 16 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 sP)) 64 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 s16P)) 64 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 s32P)) 64 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 r2P)) 16 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 u4P)) 16 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 u5P)) 128 &&
    Nat.beq (cb0P.countP (pcommAll 24 5 tP)) 64) = true := by quickRfl

theorem kC1 : Nat.beq (cb1P.countP (pcommAll 24 5 u6P)) 64 = true := by quickRfl

end CertificateChecks.KernelKGC31M24

end
