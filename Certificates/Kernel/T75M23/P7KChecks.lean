module

public import Certificates.Data.Kernel.T75M23.P7K
public import Certificates.Kernel.CosPresTab.M23Tab
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23
open CFSG.CGT.T75JM (V3 glAct matD)
open CFSG.KC.TabWord.M23 (NL)

theorem pOk_ok : pOkK NL = true := by quickRfl

theorem eCent_ok : eCentK NL = true := by quickRfl

theorem fin_a_ok : finKW pRs7a pWords7 = true := by decide +kernel

theorem fin_b_ok : finKW pRs7b [pEw7 0] = true := by decide +kernel

theorem aff_ok : AffOk := by decide +kernel

theorem tr_ok : TrOk := by decide +kernel

theorem d8_dist_ok : ∀ d : DihedralGroup 4, (∀ c, glAct (matD mS7 mR7 d) c = c) → d = 1 := by
  decide +kernel

end CFSG.KC.N7K

end
