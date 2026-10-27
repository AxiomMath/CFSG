module

public import Certificates.Data.Kernel.LocalQT.M24L
public import Certificates.Kernel.LocalQT.Core.D4119hexE
public import Certificates.Kernel.LocalQT.Core.D4119octE1
public import Certificates.Kernel.LocalQT.Core.D4119octE2
public import Certificates.Kernel.LocalQT.Core.D4119octE3
public import Certificates.Kernel.LocalQT.Core.D4119octE4
public import Certificates.Kernel.LocalQT.Core.D4119w
public import Certificates.Kernel.LocalQT.Core.D4119i3
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4119i

open CFSG.KC.LQT.W CFSG.KC.LQT.M24 CFSG.KD.LQT.C4119w

theorem pre : isetPre 24 C4119hexE.GL pWL 7 S = true := by quickRfl
theorem inS : isetIn S IL = true := by quickRfl
theorem es : allZ [C4119hexE.eWL, C4119octE1.eWL, C4119octE2.eWL, C4119octE3.eWL, C4119octE4.eWL]
    [El_hexE, El_octE1, El_octE2, El_octE3, El_octE4] (esK 24 C4119hexE.GL) = true := by quickRfl

end CFSG.KD.LQT.C4119i

end
