module

public import Certificates.Data.Kernel.T75M23.L2K7
public import Certificates.Kernel.CosPresTab.M23Tab
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23
open CFSG.KC.TabWord.M23 (NL)

theorem tK_ok : tK NL = true := by quickRfl

theorem bK_ok : bK NL = true := by quickRfl

theorem normalK_ok : normalK NL = true := by quickRfl

theorem dMemK_ok : dMemK NL = true := by quickRfl

theorem dRelK_ok : dRelK NL = true := by quickRfl

theorem abK_ok : abK NL = true := by quickRfl

theorem thSqK_ok : thSqK NL = true := by quickRfl

theorem centerK_ok : centerK NL = true := by quickRfl

end CFSG.KC.N7K

end
