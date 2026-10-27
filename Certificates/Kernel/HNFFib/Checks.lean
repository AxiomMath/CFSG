module

public import Certificates.Kernel.HNFFib.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFConst
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNFFib

open CFSG.EvenSporadicStandard.Solomon78

theorem chk5 : fibW hnfW1 hnfW2 hnfRepWords[5]! hnfRepWords[2]! F5.c F5.us F5.u 56 F5.tree F5.ord =
    true := by quickRfl

theorem chk6 : fibW hnfW1 hnfW2 hnfRepWords[6]! hnfRepWords[3]! F6.c F6.us F6.u 48 F6.tree F6.ord =
    true := by quickRfl

theorem chk8 : fibW hnfW1 hnfW2 hnfRepWords[8]! hnfRepWords[4]! F8.c F8.us F8.u 21 F8.tree F8.ord =
    true := by quickRfl

end CFSG.KD.HNFFib

end
