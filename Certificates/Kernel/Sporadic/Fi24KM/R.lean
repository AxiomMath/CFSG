module

public import Certificates.Kernel.Sporadic.Fi24KM.Prog
import CFSG.Certificates.Kernel.Common.Each

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

#kc_each CFSG.KD.KMFi24.rC 0 3

#kc_each CFSG.KD.KMFi24.mC 0 8

end
