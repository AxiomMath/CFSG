module

public import Certificates.Kernel.Sporadic.Fi24Cp.Data
import CFSG.Certificates.Kernel.Common.Each

set_option maxHeartbeats 0
set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.Fi24Cp.chk 40 50

end
