module

public import Certificates.Data.Kernel.T75JM.PCheckK
public import Certificates.Kernel.CosPresTab.M22Tab
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM
open CFSG.KC.TabWord.M22 (LP)

theorem pOk_ok : pOkK LP = true := by quickRfl

theorem eCent_ok : eCentK LP = true := by quickRfl

theorem fin_ok : finK = true := by decide +kernel

theorem aff_ok : AffOk := by decide +kernel

theorem tr_ok : TrOk := by decide +kernel

theorem d8_dist_ok : ∀ d : DihedralGroup 4, (∀ c, glAct (matD mS mR d) c = c) → d = 1 := by
  decide +kernel

end CFSG.KC.N0K

end
