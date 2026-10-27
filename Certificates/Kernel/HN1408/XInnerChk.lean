module

public import Certificates.Kernel.HN1408.XInnerDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.TabXCntDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.XInner

theorem head_ok : xiHead cds dcs wCom = true := by quickRfl

theorem scan_ok : xiScan dcs = true := by quickRfl

end CFSG.KD.HN1408.XInner

end
