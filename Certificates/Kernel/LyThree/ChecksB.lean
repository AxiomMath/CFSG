module

public import Certificates.Kernel.LyThree.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.LyThree

theorem chkB : clsW 2 3 prgB rxB sgB tbB clB cbB entB lpB abB = true := by quickRfl

end CFSG.KD.LyThree

end
