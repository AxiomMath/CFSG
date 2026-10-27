module

public import Certificates.Kernel.LocalQT.M11.C4135
public import Certificates.Data.Kernel.LocalQT.M11Perm
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4135

open CFSG.KC.Ord CFSG.KC.LQT.M

theorem hp : p4135 LI LF CFSG.KD.LQT.C4144.WI = true := by quickRfl

end CFSG.KD.LQT.C4135

end
