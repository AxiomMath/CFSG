module

public import Certificates.Kernel.LocalComp.L34GrDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LocalComp.L34NDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Gr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB)

theorem kTop : top = true := by quickRfl

theorem kY : grY (pidn 42 6) X0 = true := by quickRfl

theorem kNegY : notB (grY (pidn 42 6) (pidn 42 6)) = true := by quickRfl

theorem kNegS : notB (grS (pidn 42 6) (pidn 42 6) X0) = true := by quickRfl

theorem kNegTop : notB (allN 42 fun p => orB (Nat.beq p 1) (orB (Nat.beq p 26)
    (notB (allN 4 fun i => Nat.beq (pg 6 (mask 6) (L34Bo.syG 0 i) p) p)))) = true := by quickRfl

end CertificateChecks.KernelLC.L34Gr

end
