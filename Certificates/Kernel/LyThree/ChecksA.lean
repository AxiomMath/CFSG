module

public import Certificates.Kernel.LyThree.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.LyThree

theorem chkA : clsW 1 1 prgA rxA sgA tbA clA cbA entA lpA abA = true := by quickRfl

end CFSG.KD.LyThree

end
