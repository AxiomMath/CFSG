module

public import Certificates.Kernel.HN1408.TableIDefs
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Spor.BindList

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

#kc_each CFSG.KD.HN1408.peLS 0 10
#kc_each CFSG.KD.HN1408.hsLS 0 10
#kc_each CFSG.KD.HN1408.clLS 0 10

end
