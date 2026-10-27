module

public import Certificates.Kernel.HNFO4.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFConst
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open CFSG.EvenSporadicStandard.Solomon78

#kc_each CFSG.KD.HNFO4 c (fun i => CFSG.KD.HNFO4.chkW hnfW1 hnfW2 hnfRepWords[4]! i) 0 8
