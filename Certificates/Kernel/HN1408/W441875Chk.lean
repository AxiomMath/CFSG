module

public import Certificates.Kernel.HN1408.W441875Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.W441875Data

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.W441875

open CFSG.KC.Enum CFSG.KS

theorem ch441875_rep : allN 15 (repK RK RT RW) = true := by quickRfl

theorem ch441875_tgt : allN 5 tgtInvK = true := by quickRfl

end CFSG.KD.HN1408.W441875

end
