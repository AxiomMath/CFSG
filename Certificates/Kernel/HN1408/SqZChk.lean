module

public import Certificates.Kernel.HN1408.SqZDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#kc_each CFSG.KD.HN1408.ch26774sq sl CFSG.KD.HN1408.SqZ.sqSl 0 20

public section

namespace CFSG.KD.HN1408.SqZ

theorem named_ok : sqNamedK R = true := by quickRfl

end CFSG.KD.HN1408.SqZ

end
