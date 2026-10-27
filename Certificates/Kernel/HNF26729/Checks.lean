module

public import Certificates.Kernel.HNF26729.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFConst
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNF26729

open CFSG.EvenSporadicStandard.Solomon78

theorem chk : fullW hnfW1 hnfW2 hnfRepWords[8]! hnfStabWords[0]! hnfStabWords[1]! v tree ord =
    true := by quickRfl

end CFSG.KD.HNF26729

end
