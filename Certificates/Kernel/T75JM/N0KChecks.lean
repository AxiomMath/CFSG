module

public import Certificates.Data.Kernel.T75JM.N0K
public import Certificates.Kernel.CosPresTab.M22Tab
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM
open CFSG.KC.TabWord.M22 (LP)

theorem n0k_ok : n0kOk LP = true := by quickRfl

end CFSG.KC.N0K

end
