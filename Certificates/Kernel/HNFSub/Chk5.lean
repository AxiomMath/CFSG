module

public import Certificates.Kernel.HNFSub.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFConst
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open CFSG.EvenSporadicStandard.Solomon78

#kc_each CFSG.KD.HNFSub c (fun i => CFSG.KD.HNFSub.segW hnfW1 hnfW2 i) 120 144
