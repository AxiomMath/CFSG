module

public import Certificates.Kernel.HN1408.InvFixDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.CzTDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzInv

open CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.HNRecog

theorem fix_ok : fixK = true := by quickRfl

theorem fix_neg : (!fixPair (WK wordA) (WK wordZ) 0 127) = true := by quickRfl

theorem fix_neg_b : (!fixPair (WK wordA) (WK wordB) 1 0) = true := by quickRfl

end CFSG.KD.HN1408.CzInv

end
