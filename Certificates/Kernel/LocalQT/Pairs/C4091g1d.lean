module

public import Certificates.Kernel.LocalQT.Pairs.C4091h
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4091

open CFSG.KC.LQT.PW CFSG.KD.LQT.J2T

theorem c120 : closedS (CFSG.KC.LQT.S.getK K1G 2) K1E 0 960 = true := by quickRfl
theorem c121 : closedS (CFSG.KC.LQT.S.getK K1G 2) K1E 960 960 = true := by quickRfl
theorem c130 : closedS (CFSG.KC.LQT.S.getK K1G 3) K1E 0 960 = true := by quickRfl
theorem c131 : closedS (CFSG.KC.LQT.S.getK K1G 3) K1E 960 960 = true := by quickRfl

end CFSG.KD.LQT.C4091

end
