module

public import Certificates.Kernel.RouteP.Data.Pres
public import Certificates.Kernel.RouteP.Data.Obj
public import Certificates.Kernel.RouteP.S1.Data
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.RouteP.S1Sets

public section

namespace CFSG.KD.RouteP.S1Ck

open CFSG.KC CFSG.KC.RouteP CFSG.KD.RouteP

theorem cover : s1CoverOK NWP KAP KBP NWO KAO KBO k1Zp k1A1 k1TY k1Y 12 = true := by quickRfl

end CFSG.KD.RouteP.S1Ck

end
