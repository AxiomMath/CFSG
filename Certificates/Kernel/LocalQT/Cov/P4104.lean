module

public import Certificates.Data.Kernel.LocalQT.CovT
public import Certificates.Kernel.LocalQT.Cov.D4104
public import Certificates.Kernel.LocalQT.Cov.T4104
import CFSG.Certificates.Kernel.Common.DeepRfl

public section

namespace CFSG.KD.LQT.C4104

open CFSG.KC.LQT.Cov

theorem kParse : parseT CT.chars = some CTD := by deep_rfl 400000 256

end CFSG.KD.LQT.C4104

end
