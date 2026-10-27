module

public import Certificates.Data.Kernel.LocalQT.CovT
public import Certificates.Kernel.LocalQT.Cov.D4104
public import Certificates.Kernel.LocalQT.Cov.T4104
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.LQT.C4104

open CFSG.KC.LQT.Cov

theorem kB : covTB CT.chars H = true := by quickRfl

end CFSG.KD.LQT.C4104

end
