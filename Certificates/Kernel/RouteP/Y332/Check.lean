module

public import Certificates.Kernel.RouteP.Y332.Defs
import CFSG.Certificates.Kernel.Common.SliceRange
public import Mathlib

public section

namespace CFSG.KD.RouteP

@[expose] noncomputable def ybase9 (j : Nat) : Bool := ybase (j + 9)

@[expose] noncomputable def nkY30 (j : Nat) : Bool := nkY (j + 30)

end CFSG.KD.RouteP

#kc_slice_range CFSG.KD.RouteP.yck CFSG.KD.RouteP.Y332Ck.y 0 940
#kc_slice_range CFSG.KD.RouteP.yfix CFSG.KD.RouteP.Y332Ck.f 0 18
#kc_slice_range CFSG.KD.RouteP.ybase9 CFSG.KD.RouteP.Y332Ck.b 0 62
#kc_slice_range CFSG.KD.RouteP.ylev CFSG.KD.RouteP.Y332Ck.l 0 8
#kc_slice_range CFSG.KD.RouteP.nkY30 CFSG.KD.RouteP.Y332Ck.n 0 82

end
