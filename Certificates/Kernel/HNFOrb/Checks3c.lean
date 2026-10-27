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

#kc_each CFSG.KD.HNFOrb c3_
  (fun j => chunkW hnfW1 hnfW2 hnfRepWords[3]! O3.u (getL O3.mv j) (getL O3.ks j)) 20 29

theorem d3 : distOK (flat O3.ks) O3.ord 5775 = true := by quickRfl

end CFSG.KD.HNFOrb

end
