module

public import Certificates.Kernel.HNFOrb.Lits
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNFOrb

open CFSG.KC.HNFOrb

#kc_each CFSG.KD.HNFOrb c2_
  (fun j => chunkL BT2 O2.u (getL O2.mv j) (getL O2.ks j)) 0 33

theorem d2 : distOK (flat O2.ks) O2.ord 2200 = true := by quickRfl

end CFSG.KD.HNFOrb

end
