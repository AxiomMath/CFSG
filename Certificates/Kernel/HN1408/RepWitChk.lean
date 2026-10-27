module

public import Certificates.Kernel.HN1408.RepWitDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzInv

theorem rep_wit_ok : repWitK = true := by quickRfl

theorem rep_wit_neg_target : (!witK 5 2 [1, 3, 4, 3, 5, 0, 1]) = true := by quickRfl

theorem rep_wit_neg_letter : (!witK 5 1 [1, 3, 4, 3, 5, 0, 2]) = true := by quickRfl

theorem rep_wit_neg_range : (!witK 5 1 [1, 3, 4, 3, 5, 0, 1, 7]) = true := by quickRfl

theorem rep_wit_neg_class : (!witK 6 1 [1, 3, 4, 3, 5, 0, 1]) = true := by quickRfl

end CFSG.KD.HN1408.CzInv

end
