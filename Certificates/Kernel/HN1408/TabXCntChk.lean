module

public import Certificates.Kernel.HN1408.TabXCntDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.CzTDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TabX

open CFSG.KC.Enum CFSG.KS CFSG.KD.HN1408.CzT CFSG.EvenSporadicStandard.HNRecog

theorem stab0_ok : stabK (WK wordB) 768 = true := by quickRfl

theorem stab1_ok : stabK (pc (T0 817) (T1 0)) 384 = true := by quickRfl

end CFSG.KD.HN1408.TabX

end
