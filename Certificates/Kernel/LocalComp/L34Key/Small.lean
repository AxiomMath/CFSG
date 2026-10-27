module

public import Certificates.Kernel.LocalComp.L34Key.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Key

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34Key
open CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB notB)

theorem kInv9304 : allN 64 (fun c => andB (canonK 42 6 (mask 6) (42 * 6) (ci9304 c))
    (Nat.beq (pcomp 42 6 (mask 6) (L34C1.P c) (ci9304 c)) (pidn 42 6))) = true := by
  quickRfl

theorem kCQ9304 : cqK 42 6 64 L34C1.P ci9304 (RP 0) = true := by quickRfl

theorem kNeg9304 : andB (notB (cqK 42 6 64 L34C1.P ci9304 (pidn 42 6)))
    (notB (keyK 42 6 64 L34C1.P (pidn 42 6) (L34R.T 0))) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34Key

end
