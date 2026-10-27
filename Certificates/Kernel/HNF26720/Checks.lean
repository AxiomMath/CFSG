module

public import Certificates.Kernel.HNF26720.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFConst
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNF26720

open CFSG.EvenSporadicStandard.Solomon78

theorem c1 : commW hnfW1 = true := by quickRfl

theorem c2 : commW hnfW2 = true := by quickRfl

theorem p0 : pairW hnfRepWords[0]! 0 = true := by quickRfl

theorem p1 : pairW hnfRepWords[1]! 1 = true := by quickRfl

theorem p2 : pairW hnfRepWords[2]! 2 = true := by quickRfl

theorem p3 : pairW hnfRepWords[3]! 3 = true := by quickRfl

theorem p4 : pairW hnfRepWords[4]! 4 = true := by quickRfl

theorem p5 : pairW hnfRepWords[5]! 5 = true := by quickRfl

theorem p6 : pairW hnfRepWords[6]! 6 = true := by quickRfl

theorem p7 : pairW hnfRepWords[7]! 7 = true := by quickRfl

theorem p8 : pairW hnfRepWords[8]! 8 = true := by quickRfl

theorem dist : distOK = true := by quickRfl

end CFSG.KD.HNF26720

end
