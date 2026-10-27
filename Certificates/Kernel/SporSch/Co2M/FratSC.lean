
module

public import Certificates.Kernel.SporSch.Co2M.FratSD
public import Certificates.Kernel.SporSch.Co2M.ChainSD
public import Certificates.Kernel.SporSch.Co2M.FratTr
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

theorem sq_ok : allN 15 (fun j => siftF (pc (Co2LS.S j) (Co2LS.S j))) = true := by
  quickRfl

theorem pair_ok : allN 32 (fun u => allN 32 fun v =>
    bIf(Nat.blt u v, bIf(siftF (pc (FY (Nat.add 32 u)) (FY v)), false, true), true)) = true := by
  quickRfl

theorem canon_ok : (allN 15 (fun j => bAnd(canonK 2300 12 (mask 12) (2300 * 12) (Co2LS.S j),
    canonK 2300 12 (mask 12) (2300 * 12) (Co2LS.SI j))) &&
    allN 12 (fun k => canonK 2300 12 (mask 12) (2300 * 12) (Co2LF.S k)) &&
    allN 64 (fun k => canonK 2300 12 (mask 12) (2300 * 12) (FY k))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
