module

public import Certificates.Kernel.J27031.M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.DcKN

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.J27031.CV1

open CFSG.KC.DcK

@[expose] noncomputable def G : Nat → Nat → Nat := K.vg (exOf ab w1)

theorem hd : enumHd 315 BK 1930 EV1 = true := by quickRfl

theorem s0 : elemsK 315 BK G 4 EV1 0 960 = true := by quickRfl

theorem s1 : elemsK 315 BK G 4 EV1 960 960 = true := by quickRfl

end CFSG.KD.J27031.CV1

end
