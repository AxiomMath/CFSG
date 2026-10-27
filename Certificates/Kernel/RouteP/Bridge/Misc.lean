module

public import Certificates.Kernel.RouteP.Bridge.Defs
import CFSG.Certificates.Kernel.Common.SliceRange
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Presentation.Common
public import Mathlib

public section

#kc_slice_range CFSG.KD.RouteP.nkP CFSG.KD.RouteP.BridgeCk.n 0 42
#kc_slice_range CFSG.KD.RouteP.zck CFSG.KD.RouteP.BridgeCk.z 0 20

namespace CFSG.KD.RouteP.BridgeCk

theorem trans : CFSG.KD.RouteP.transOK = true := by quickRfl

theorem zp : CFSG.KD.RouteP.zpOK = true := by quickRfl

end CFSG.KD.RouteP.BridgeCk

end
