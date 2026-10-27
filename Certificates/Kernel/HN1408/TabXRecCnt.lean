module

public import Certificates.Kernel.HN1408.TabXRecDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.TabXCntDefs

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch441697 cnt CFSG.KD.HN1408.TabX.cntOK 0 11

public section

namespace CFSG.KD.HN1408.TabX

theorem sq_ok : sqK = true := by quickRfl

end CFSG.KD.HN1408.TabX

end
