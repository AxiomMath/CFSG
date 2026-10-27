
module

public import Certificates.Kernel.SporSch.Co2M.FratSD
public import Certificates.Kernel.SporSch.Co2M.ChainSD
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum

theorem conj_ok : allN 15 (fun j => allN 12 fun k =>
    siftF (pc (pc (Co2LS.S j) (Co2LF.S k)) (Co2LS.SI j))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
