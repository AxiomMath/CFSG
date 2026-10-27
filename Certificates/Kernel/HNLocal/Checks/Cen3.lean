module

public import Certificates.Kernel.HNLocal.Data
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

theorem ce6 : CFSG.KC.HNLocal.cenAt mul vm PC RP TG (nat_lit 0x20) CFSG.KD.OrdHN.ONE CFSG.KD.OrdHN.RM
    (nat_lit 0x6) (nat_lit 0x4) (nat_lit 0xa) = true := by
  quickRfl

theorem ce7 : CFSG.KC.HNLocal.cenAt mul vm PC RP TG (nat_lit 0x20) CFSG.KD.OrdHN.ONE CFSG.KD.OrdHN.RM
    (nat_lit 0x7) (nat_lit 0x4) (nat_lit 0xa) = true := by
  quickRfl

end CFSG.KD.HNLocal

end
