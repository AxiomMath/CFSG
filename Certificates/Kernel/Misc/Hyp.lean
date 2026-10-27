module

public import Certificates.Kernel.Misc.HypData
public import Certificates.Kernel.Misc.HypD.LB
public import Certificates.Kernel.Misc.HypD.LI
public import Certificates.Kernel.Misc.HypD.WT
public import Certificates.Kernel.Misc.HypD.GI
public import Certificates.Kernel.Misc.XiD.TP
public import Certificates.Kernel.Misc.XiD.HS
public import Certificates.Kernel.Misc.XiD.ML
public import Certificates.Kernel.Misc.LinesData
public import Certificates.Kernel.Misc.T46Data
public import Certificates.Data.Kernel.Misc.Hyp
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Misc.Hyp

open CFSG.KC.Misc.Hyp CFSG.KD.Misc.T46 CFSG.KD.Misc.Lines CFSG.KD.Misc.Xi

theorem lamOK : lamOKK UP PP PB LB PL [76, 307, 51, 217, 67] = true := by quickRfl
theorem words : wordsK TP WT GI QB PW = true := by quickRfl
theorem rootC : rootCK TP HS ML = true := by quickRfl
theorem lamAll : ∀ k < 32, lamK UP PP TP LB [76, 307, 51, 217, 67] (32 * k) 32 = true := by
  kc_cover 1
theorem liAll : ∀ k < 16, liK LB LI (64 * k) 64 = true := by kc_cover 1
theorem rootLAll : ∀ k < 21, rootLK UP PP HS PL (33 * k) 33 = true := by kc_cover 1
theorem nlAll : ∀ k < 21, nlK GI PL NL (33 * k) 33 = true := by kc_cover 1

end CFSG.KD.Misc.Hyp

end
