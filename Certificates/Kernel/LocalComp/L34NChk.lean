module

public import Certificates.Kernel.LocalComp.L34NDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34N

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34Norm
open CFSG.KLie.CT (andB notB)

theorem kEnds : andB (Nat.beq (C 0) 0) (Nat.beq (C 180) 7755) = true := by
  quickRfl

theorem kCanonK : allN 12 (fun j => canonK 42 6 (mask 6) (42 * 6) (K j)) = true := by
  quickRfl

theorem kNeg1 : notB (strictB (pidn 42 6) fun e => curSl (fun k =>
    normCode 42 6 9 AP (K 0) (K 1) (K 0) 1 27 e (L34R.T k)) J 1344 C 0) = true := by
  quickRfl

theorem kNeg2 : notB (strictB (pidn 42 6) fun e => curSl (fun k =>
    normCode 42 6 9 AP (K 0) (K 1) (K 2) 1 2 e (L34R.T k)) J 1344 C 0) = true := by
  quickRfl

theorem kNeg3 : notB (strictB (pidn 42 6) fun e => curSl (code e) (fun q => J q + 8) 1344 C 0) =
    true := by
  quickRfl

end CertificateChecks.KernelLC.L34N

end
