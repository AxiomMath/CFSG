module

public import Certificates.Kernel.RouteP.Ronan.Data
public import Certificates.Data.Kernel.RouteP.RonanRoot
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.RouteP.RonanCk

open CFSG.KC CFSG.KC.RouteP CFSG.KD.RouteP

theorem root0 : rootOK RE 0 7 = true := by quickRfl

theorem root2 : rootOK RE 26 71 = true := by quickRfl

theorem root4 : rootOK RE 105 149 = true := by quickRfl

theorem neg_root : notB (rootOK RE 0 26) = true := by quickRfl

end CFSG.KD.RouteP.RonanCk

end
