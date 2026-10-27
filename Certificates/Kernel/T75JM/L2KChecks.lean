module

public import Certificates.Data.Kernel.T75JM.L2K
public import Certificates.Kernel.CosPresTab.M22Tab
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM
open CFSG.KC.TabWord.M22 (LP)

theorem tK_ok : tK LP = true := by quickRfl

theorem bK_ok : bK LP = true := by quickRfl

theorem aRelK_ok : aRelK LP = true := by quickRfl

theorem aTK_ok : aTK LP = true := by quickRfl

theorem dMemK_ok : dMemK LP = true := by quickRfl

theorem dRelK_ok : dRelK LP = true := by quickRfl

theorem abK_ok : abK LP = true := by quickRfl

theorem thSqK_ok : thSqK LP = true := by quickRfl

theorem normalK_ok : normalK LP = true := by quickRfl

theorem alphaK_ok : alphaK LP = true := by quickRfl

theorem centerK_ok : centerK LP = true := by quickRfl

end CFSG.KC.N0K

end
