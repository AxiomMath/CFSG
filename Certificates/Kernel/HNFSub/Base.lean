module

public import Certificates.Kernel.HNFSub.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFConst
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[expose] public section

namespace CFSG.KD.HNFSub

open CFSG.EvenSporadicStandard.Solomon78

theorem base : baseW hnfRepWords[7]! 0 = true := by quickRfl

theorem fib : fibW hnfW1 hnfW2 hnfRepWords[7]! 4 = true := by quickRfl

end CFSG.KD.HNFSub

end
