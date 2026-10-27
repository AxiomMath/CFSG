module

public import Certificates.Kernel.HN1408.TransDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words
public import Certificates.Kernel.HN1408.TransData

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Trans

open CFSG.KC.Enum CFSG.KS

theorem trans_ok : transK TR = true := by quickRfl

theorem neg_trans : (!transK (fun q => nIf(Nat.beq q 5, Nat.add (TR q) 65536, TR q))) = true := by
  quickRfl

end CFSG.KD.HN1408.Trans

end
