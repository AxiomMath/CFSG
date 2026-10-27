module

public import Certificates.Kernel.HeIdx.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.EmptyFaithful.S151S9THeInputs
public import Certificates.Data.Kernel.S151IdxF

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HeIdx

open CFSG.KC.IdxF CFSG.Quasithin.S151S9T

theorem idx3_ok : idx3OkF heWit1 8330 CFSG.KD.HeDc.Δ 11 4 mlen CFSG.KD.HeDc.Lm Sl Z = true := by
  quickRfl

end CFSG.KD.HeIdx

end
