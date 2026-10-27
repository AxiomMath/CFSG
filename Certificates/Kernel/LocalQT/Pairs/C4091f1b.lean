module

public import Certificates.Kernel.LocalQT.Pairs.C4091f1
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KD.LQT.J2T

theorem f14 : f1S 4 = true := by quickRfl
theorem f15 : f1S 5 = true := by quickRfl
theorem f16 : f1S 6 = true := by quickRfl
theorem f17 : f1S 7 = true := by quickRfl

end CFSG.KD.LQT.C4091

end
