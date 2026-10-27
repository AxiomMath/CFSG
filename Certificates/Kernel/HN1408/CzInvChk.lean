module

public import Certificates.Kernel.HN1408.CzInvDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch26771inv sl CFSG.KD.HN1408.CzInv.invSl 0 20

public section

namespace CFSG.KD.HN1408.CzInv

theorem named_ok : namedK R = true := by quickRfl

end CFSG.KD.HN1408.CzInv

end
