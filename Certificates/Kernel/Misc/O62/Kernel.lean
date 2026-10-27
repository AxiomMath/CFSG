module

public import Certificates.Kernel.Misc.O62.Data
public import CFSG.LargeExtraspecial.O62Data

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Misc.O62

open CFSG.KC.Misc.O62 CFSG.LargeExtraspecial.O62

theorem sylowP : sylowK 0 sylowWordsPlus CSP = true := by decide +kernel
theorem rankPreP : rankPre CSP ILP IPP = true := by decide +kernel
theorem cntPP : Nat.beq (plCnt IPP) 43 = true := by decide +kernel
theorem cntQP : Nat.beq (plCnt IQP) 43 = true := by decide +kernel
theorem invParP : wcPre sylowWordsPlus IQP = true := by decide +kernel
theorem certP : certK certsPlus EPP = true := by decide +kernel
theorem rxP : CFSG.KC.LQT.P.allN 43 (rankX IPP) = true := by decide +kernel
theorem wxP : CFSG.KC.LQT.P.allN 43 (wcX 0 IQP certsPlus EPP) = true := by decide +kernel

theorem sylowM : sylowK 1 sylowWordsMinus CSM = true := by decide +kernel
theorem rankPreM : rankPre CSM ILM IPM = true := by decide +kernel
theorem cntPM : Nat.beq (plCnt IPM) 43 = true := by decide +kernel
theorem cntQM : Nat.beq (plCnt IQM) 43 = true := by decide +kernel
theorem invParM : wcPre sylowWordsMinus IQM = true := by decide +kernel
theorem certM : certK certsMinus EPM = true := by decide +kernel
theorem rxM : CFSG.KC.LQT.P.allN 43 (rankX IPM) = true := by decide +kernel
theorem wxM : CFSG.KC.LQT.P.allN 43 (wcX 1 IQM certsMinus EPM) = true := by decide +kernel

end CFSG.KD.Misc.O62

end
