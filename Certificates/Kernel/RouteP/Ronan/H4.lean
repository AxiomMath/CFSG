module

public import Certificates.Kernel.RouteP.Ronan.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.RouteP.RonanCk

open CFSG.KC.RouteP

theorem h4 : h4OK NWP KAP KBP NWO KAO KBO NWC KAC KBC RN = true := by quickRfl

theorem n4a : n4OK NWP KAP KBP RN (gMW 5) = true := by quickRfl

theorem n4b : n4OK NWP KAP KBP RN (gMW 6) = true := by quickRfl

end CFSG.KD.RouteP.RonanCk

end
