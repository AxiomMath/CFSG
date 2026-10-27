module

public import Certificates.Kernel.GH74Tab.Cf
public import CFSG.Certificates.Kernel.GH74Tab.Cf

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab CFSG.GH74.GLS.C3.Layer2.Model

theorem c5042_cfSetE1_6 : (cfSetE1 6).card = 64 := by
  rw [card_cfSetE1]
  exact c5042_cfLen6

theorem c5042_cfSetE1_7 : (cfSetE1 7).card = 192 := by
  rw [card_cfSetE1]
  exact c5042_cfLen7

theorem c5042_cfCoverE1_6 : (mkTab 6).cfCoverE1 = true := by
  rw [cfCoverE1_eq]
  exact c5042_cfCov6

theorem c5042_cfCoverE1_7 : (mkTab 7).cfCoverE1 = true := by
  rw [cfCoverE1_eq]
  exact c5042_cfCov7

end CFSG.KD.GH74Tab

end
