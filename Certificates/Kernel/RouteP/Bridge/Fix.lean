module

public import Certificates.Kernel.RouteP.Bridge.Defs
import CFSG.Certificates.Kernel.Common.SliceRange
public import CFSG.Sporadic.Presentation.Common
public import Mathlib

public section

namespace CFSG.KD.RouteP

@[expose] noncomputable def fixck (j : Nat) : Bool := CFSG.KC.RouteP.ptOK NWP KAP KBP [zpL[j]!] 0 0

end CFSG.KD.RouteP

#kc_slice_range CFSG.KD.RouteP.fixck CFSG.KD.RouteP.BridgeCk.f 0 10

end
