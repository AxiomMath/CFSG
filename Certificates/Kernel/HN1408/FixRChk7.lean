module

public import Certificates.Kernel.HN1408.FixRDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch26775f7 rep CFSG.KD.HN1408.FixR.f7Rep 0 3
#kc_each CFSG.KD.HN1408.ch26775f7 srt CFSG.KD.HN1408.FixR.f7Sort 0 17

public section

namespace CFSG.KD.HN1408.FixR

theorem f7_head : f7Head = true := by quickRfl

end CFSG.KD.HN1408.FixR

end
