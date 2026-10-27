module

public import Certificates.Kernel.HN1408.FixRDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch26775f3 rep CFSG.KD.HN1408.FixR.f3Rep 0 5
#kc_each CFSG.KD.HN1408.ch26775f3 srt CFSG.KD.HN1408.FixR.f3Sort 0 2

public section

namespace CFSG.KD.HN1408.FixR

theorem f3_head : f3Head = true := by quickRfl

end CFSG.KD.HN1408.FixR

end
