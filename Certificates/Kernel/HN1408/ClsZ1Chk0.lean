module

public import Certificates.Kernel.HN1408.ClsRDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Words

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch26771cz rep CFSG.KD.HN1408.ClsR.z1Rep 0 14

public section

namespace CFSG.KD.HN1408.ClsR

open CFSG.EvenSporadicStandard.HNRecog

theorem z1_root : rootK wordZ₁ ClsZ1.R = true := by quickRfl

end CFSG.KD.HN1408.ClsR

end
