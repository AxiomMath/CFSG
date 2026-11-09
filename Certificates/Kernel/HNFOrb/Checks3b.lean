module

public import Certificates.Kernel.HNFOrb.Lits
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNFOrb

open CFSG.KC.HNFOrb

#kc_each CFSG.KD.HNFOrb c3_
  (fun j => chunkL BT3 O3.u (getL O3.mv j) (getL O3.ks j)) 29 58

end CFSG.KD.HNFOrb

end
