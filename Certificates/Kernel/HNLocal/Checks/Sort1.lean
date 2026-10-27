module

public import Certificates.Kernel.HNLocal.XData
public import Certificates.Kernel.HNLocal.SortData
public import Certificates.Kernel.HNLocal.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

theorem so1 : CFSG.KC.HNLocal.sortRange XC SD (nat_lit 0x116520) M (nat_lit 0x85f) (nat_lit 0x85f) =
    true := by
  quickRfl

end CFSG.KD.HNLocal

end
