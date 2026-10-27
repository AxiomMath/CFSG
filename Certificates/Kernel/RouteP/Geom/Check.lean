module

public import Certificates.Kernel.RouteP.Data.Pres
public import Certificates.Kernel.RouteP.Data.Obj
public import Certificates.Data.Kernel.RouteP.Geom
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.RouteP.GeomCk

open CFSG.KC.RouteP

theorem geomSet : geomSetOK NWP KAP KBP NWO KAO KBO [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]
    [-7, -8, -9] = true := by quickRfl

end CFSG.KD.RouteP.GeomCk

end
