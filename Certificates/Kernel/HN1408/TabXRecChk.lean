module

public import Certificates.Kernel.HN1408.TabXRecDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.TabXCntDefs

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch441697 dsl CFSG.KD.HN1408.TabX.dSl 0 30

public section

namespace CFSG.KD.HN1408.TabX

theorem r_ok : rAll = true := by quickRfl

theorem dgens_ok : dGensK = true := by quickRfl

theorem norm_ok : normK = true := by quickRfl

theorem quot_ok : quotK = true := by quickRfl

theorem rgens_ok : rGensK = true := by quickRfl

theorem named_ok : namedK = true := by quickRfl

theorem z_ok : zK = true := by quickRfl

theorem sig_ok : sigK = true := by quickRfl

end CFSG.KD.HN1408.TabX

end
