module

public import Certificates.Data.Kernel.GH74Tab.Cf

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab CFSG.GH74.GLS.C3.Layer2.Model

theorem c5042_cfLen6 : (cfF 6).length = 64 := by decide +kernel

theorem c5042_cfLen7 : (cfF 7).length = 192 := by decide +kernel

theorem c5042_cfCov6 : cfCovF (mkTab 6) (repListE1 6) = true := by decide +kernel

theorem c5042_cfCov7 : cfCovF (mkTab 7) (repListE1 7) = true := by decide +kernel

end CFSG.KD.GH74Tab

end
