module

public import Certificates.Kernel.SporSch.PairHS.Chain
public import Certificates.Kernel.SporSch.Pair.HSCert
public import Certificates.Data.Kernel.SporSch.PairK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PHSCheck

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CertificateChecks.KernelSporSch

theorem sEq : allN 8 (fun j => Nat.beq (PHSC.S j) (PHS j)) = true := by quickRfl

theorem perm : allN 8 (fun j => permOK 3850 12 (mask 12) (3850 * 12) (PHSC.S j) (PHSC.SI j)) =
    true := by
  quickRfl

theorem canonOK : allN 2 (fun j => bAnd(canonK 3850 12 (mask 12) (3850 * 12) (PHSC.S j),
    canonK 3850 12 (mask 12) (3850 * 12) (PHSC.SI j))) = true := by
  quickRfl

theorem idOK : bAnd(canonK 3850 12 (mask 12) (3850 * 12) (pidn 3850 12), idK 3850 12 (mask 12)) =
    true := by
  quickRfl

end CertificateChecks.KernelSporSch.PHSCheck

end
