module

public import Certificates.Kernel.HN1408.TableIDefs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Spor.BindList

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

#kc_each CFSG.KD.HN1408.pe1 0 4
#kc_each CFSG.KD.HN1408.hv1 0 2

namespace CFSG.KD.HN1408

theorem kS1 : hs1 = true := by quickRfl

end CFSG.KD.HN1408

end
