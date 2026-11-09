module

public import Certificates.Kernel.HNFOrb.Lits
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNFOrb

open CFSG.KC.HNFOrb

#kc_each CFSG.KD.HNFOrb c1_
  (fun j => chunkL BT1 O1.u (getL O1.mv j) (getL O1.ks j)) 0 19

theorem d1 : distOK (flat O1.ks) O1.ord 1408 = true := by quickRfl

end CFSG.KD.HNFOrb

end
