module

public import Certificates.Kernel.HN1408.FixRDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch26775f5b rep CFSG.KD.HN1408.FixR.f5bRep 0 17
#kc_each CFSG.KD.HN1408.ch26775f5b srt CFSG.KD.HN1408.FixR.f5bSort 0 5

public section

namespace CFSG.KD.HN1408.FixR

theorem f5b_head : f5bHead = true := by quickRfl

end CFSG.KD.HN1408.FixR

end
