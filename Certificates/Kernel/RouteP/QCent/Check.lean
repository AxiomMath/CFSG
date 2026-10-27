module

public import Certificates.Kernel.RouteP.Data.Pres
public import Certificates.Kernel.RouteP.Plane.Defs
public import Certificates.Data.Kernel.RouteP.QCentSet
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.RouteP.QCentCk

open CFSG.KC.RouteP CFSG.KD.RouteP

theorem qcentSet : qcentSetOK NWP KAP KBP NWO KAO KBO NWQ KAQ KBQ
    [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] ((List.range 14).map zl) = true := by quickRfl

end CFSG.KD.RouteP.QCentCk

end
