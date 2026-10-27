
module

public import Certificates.Kernel.SporSch.Co2M.FratSD
public import Certificates.Kernel.SporSch.Co2M.ChainSD
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum

theorem comm_ok : allN 15 (fun i => allN 15 fun j =>
    siftF (pc (pc (pc (Co2LS.S i) (Co2LS.S j)) (Co2LS.SI i)) (Co2LS.SI j))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
