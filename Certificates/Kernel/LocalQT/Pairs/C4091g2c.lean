module

public import Certificates.Kernel.LocalQT.Pairs.C4091h
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KD.LQT.J2T

theorem c20 : closedS (CFSG.KC.LQT.S.getK K2G 0) K2E 0 1152 = true := by quickRfl
theorem c21 : closedS (CFSG.KC.LQT.S.getK K2G 1) K2E 0 1152 = true := by quickRfl
theorem c22 : closedS (CFSG.KC.LQT.S.getK K2G 2) K2E 0 1152 = true := by quickRfl
theorem c23 : closedS (CFSG.KC.LQT.S.getK K2G 3) K2E 0 1152 = true := by quickRfl

end CFSG.KD.LQT.C4091

end
