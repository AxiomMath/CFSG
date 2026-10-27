module

public import Certificates.Kernel.HN1408.FixRDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch26775f5c rep CFSG.KD.HN1408.FixR.f5cRep 0 8
#kc_each CFSG.KD.HN1408.ch26775f5c srt CFSG.KD.HN1408.FixR.f5cSort 0 3

public section

namespace CFSG.KD.HN1408.FixR

theorem f5c_head : f5cHead = true := by quickRfl

end CFSG.KD.HN1408.FixR

end
