module

public import Certificates.Kernel.LyFivePc.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.LyFivePc

theorem chkX : clsW XX prgX rxX sgX rel entX lpX abX = true := by quickRfl

end CFSG.KD.LyFivePc

end
