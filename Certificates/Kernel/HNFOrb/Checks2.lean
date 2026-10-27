module

public import Certificates.Kernel.HNFOrb.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFConst
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNFOrb

open CFSG.KC.HNFOrb CFSG.EvenSporadicStandard.Solomon78

#kc_each CFSG.KD.HNFOrb c2_
  (fun j => chunkW hnfW1 hnfW2 hnfRepWords[2]! O2.u (getL O2.mv j) (getL O2.ks j)) 0 11

theorem d2 : distOK (flat O2.ks) O2.ord 2200 = true := by quickRfl

end CFSG.KD.HNFOrb

end
