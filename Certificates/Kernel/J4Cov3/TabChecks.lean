module

public import Certificates.Kernel.J4Cov3.TabData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.J4Cov3

theorem chk : chkW prg rp cj cw fu prg2 xr = true := by quickRfl

end CFSG.KD.J4Cov3

end
