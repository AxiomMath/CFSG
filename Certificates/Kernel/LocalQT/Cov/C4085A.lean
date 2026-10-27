module

public import Certificates.Data.Kernel.LocalQT.CovH
public import Certificates.Kernel.LocalQT.Cov.D4085
public import Certificates.Kernel.LocalQT.Cov.T4085
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.LQT.C4085

open CFSG.KC.LQT.Cov

theorem kA : covHA 3850 12 (HS.F 0) (HS.F 1) CT.chars P 512 = true := by quickRfl

end CFSG.KD.LQT.C4085

end
