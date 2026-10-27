module

public import Certificates.Kernel.LocalComp.L34Idx.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LocalComp.L34T3.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Idx

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (andB orB notB)

theorem kZ : andB (allN 4 fun j => commPt 42 6 (L34PT.T 5) (L34PT.G j))
    (allN 4 fun j => commPt 42 6 (L34PT.T 51) (L34PT.G j)) = true := by quickRfl

theorem kTS : allN 64 (fun i => strictB (L34IX.TS i) fun q =>
    andB (Nat.blt q 20160) (Nat.beq (L34S.T q) (L34PT.T i))) = true := by quickRfl

theorem kY : allN 48 (fun q => andB (canonK 42 6 (mask 6) (42 * 6) (L34IX.Y q))
    (andB (canonK 42 6 (mask 6) (42 * 6) (L34IX.YI q))
      (Nat.beq (pcomp 42 6 (mask 6) (L34IX.Y q) (L34IX.YI q)) (pidn 42 6)))) = true := by
  quickRfl

theorem kP0 : pairRows 0 24 = true := by quickRfl

theorem kP1 : pairRows 24 24 = true := by quickRfl

end CertificateChecks.KernelLC.L34Idx

end
