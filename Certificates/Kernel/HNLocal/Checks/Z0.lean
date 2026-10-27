module

public import Certificates.Kernel.HNLocal.ZData
import CFSG.Certificates.Kernel.Common.Each

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocalZ

#kc_each CFSG.KD.HNLocalZ.zChunk 0 4

end CFSG.KD.HNLocalZ

end
