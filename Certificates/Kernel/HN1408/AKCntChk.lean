module

public import Certificates.Kernel.HN1408.AKCnt
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Defs
public import Certificates.Kernel.HN1408.M11Words

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.AK

open CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408

theorem cnt_ok : cntK = true := by quickRfl

end CFSG.KD.HN1408.AK

end
