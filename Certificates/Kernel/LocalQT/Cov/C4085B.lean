module

public import Certificates.Data.Kernel.LocalQT.CovH
public import Certificates.Kernel.LocalQT.Cov.D4085
public import Certificates.Kernel.LocalQT.Cov.T4085
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.LQT.C4085

open CFSG.KC.LQT.Cov

theorem kB : covHB CT.chars H = true := by quickRfl

end CFSG.KD.LQT.C4085

end
