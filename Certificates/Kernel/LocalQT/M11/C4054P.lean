module

public import Certificates.Kernel.LocalQT.M11.C4054
public import Certificates.Data.Kernel.LocalQT.M11Perm
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4054

open CFSG.KC.Ord CFSG.KC.LQT.M

theorem hp : p4054 RO T0 S0 C0 = true := by quickRfl

end CFSG.KD.LQT.C4054

end
