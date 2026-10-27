module

public import Certificates.Kernel.HN1408.FixRDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch26775f5a rep CFSG.KD.HN1408.FixR.f5aRep 0 2
#kc_each CFSG.KD.HN1408.ch26775f5a srt CFSG.KD.HN1408.FixR.f5aSort 0 1

public section

namespace CFSG.KD.HN1408.FixR

theorem f5a_head : f5aHead = true := by quickRfl

end CFSG.KD.HN1408.FixR

end
