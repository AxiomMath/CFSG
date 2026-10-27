module

public import Certificates.Kernel.HN1408.M11Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408

open CFSG.EvenSporadicStandard.HNRecog

theorem kCZ : clsK classz.rep MRZ MPZ MSZ MWZ 525 5775 = true := by quickRfl

end CFSG.KD.HN1408

end
