module

public import Certificates.Kernel.HNLocal.Checks.CenV0
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

theorem ceD0m : CFSG.KC.HNLocal.cenDL mul vm PC RP TG (nat_lit 0x20) CFSG.KD.OrdHN.ONE
    CFSG.KD.OrdHN.RM (nat_lit 0xe) D0m = true := by
  quickRfl

end CFSG.KD.HNLocal

end
