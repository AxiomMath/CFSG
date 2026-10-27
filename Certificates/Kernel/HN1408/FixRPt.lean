module

public import Certificates.Kernel.HN1408.FixRDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.FixR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

theorem f3_pt0 : Nat.beq (pt (Fix3.R 0) 0) 0 = true := by quickRfl
theorem f5a_pt0 : Nat.beq (pt (Fix5a.R 0) 0) 0 = true := by quickRfl
theorem f5b_pt0 : Nat.beq (pt (Fix5b.R 0) 0) 0 = true := by quickRfl
theorem f5c_pt0 : Nat.beq (pt (Fix5c.R 0) 0) 0 = true := by quickRfl
theorem f7_pt0 : Nat.beq (pt (Fix7.R 0) 0) 0 = true := by quickRfl

end CFSG.KD.HN1408.FixR

end
