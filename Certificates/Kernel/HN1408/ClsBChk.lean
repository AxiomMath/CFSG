module

public import Certificates.Kernel.HN1408.ClsRDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch26771cb rep CFSG.KD.HN1408.ClsR.bRep 0 4
#kc_each CFSG.KD.HN1408.ch26771cb srt CFSG.KD.HN1408.ClsR.bSort 0 4

public section

namespace CFSG.KD.HN1408.ClsR

open CFSG.EvenSporadicStandard.HNRecog

theorem b_root : rootK wordB ClsB.R = true := by quickRfl

end CFSG.KD.HN1408.ClsR

end
