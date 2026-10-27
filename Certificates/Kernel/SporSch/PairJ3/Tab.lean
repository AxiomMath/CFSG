
module

public import Certificates.Kernel.SporSch.PairJ3.Chain
public import Certificates.Data.Kernel.SporSch.PairK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PJ3Check

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CertificateChecks.KernelSporSch

theorem tab : hexTabK PJ3Text.chars 4 6156 13 5 PJ3.S = true := by quickRfl

theorem perm : allN 5 (fun j => permOK 6156 13 (mask 13) (6156 * 13) (PJ3.S j) (PJ3.SI j)) =
    true := by
  quickRfl

theorem canonOK : allN 2 (fun j => bAnd(canonK 6156 13 (mask 13) (6156 * 13) (PJ3.S j),
    canonK 6156 13 (mask 13) (6156 * 13) (PJ3.SI j))) = true := by
  quickRfl

theorem idOK : bAnd(canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13), idK 6156 13 (mask 13)) =
    true := by
  quickRfl

end CertificateChecks.KernelSporSch.PJ3Check

end
