module

public import Certificates.Data.Kernel.T75JM.L2KD
public import Certificates.Kernel.CosPresTab.M22Tab
public import Certificates.Kernel.T75JM.L2KData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM
open CFSG.KC.TabWord.M22 (LP)

theorem icK_ok : icK LP CFSG.KD.T75JML2.ic = true := by quickRfl

end CFSG.KC.N0K

end
