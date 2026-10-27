module

public import Certificates.Kernel.HN1408.M11Defs
import CFSG.Certificates.Kernel.Common.Each
public import Certificates.Kernel.HN1408.M11Words

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

#kc_each CFSG.KD.HN1408.clA 0 8

end
