module

public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNLocalV
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

theorem ce1 : CFSG.KC.HNLocal.cenVAt vm PC TG (nat_lit 0x0)
    (nat_lit 0x1) (nat_lit 0x4) (nat_lit 0xa) = true := by
  quickRfl

end CFSG.KD.HNLocal

end
