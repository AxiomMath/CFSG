module

public import CFSG.Certificates.Kernel.Orders.Cert3
public import Certificates.Kernel.Sporadic.Fi24Br.Prog
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.BrFi24

theorem consts : CFSG.KC.Ord.consts3OK (nat_lit 781) (nat_lit 11) (nat_lit 609961) LO RM CI ONE UP =
    true := by
  quickRfl

theorem hroots : CFSG.KC.Ord.rootsOK RB VLD (nat_lit 1) (nat_lit 12) = true := by quickRfl

end CFSG.KD.BrFi24

#kc_each CFSG.KD.BrFi24.ivC 0 11

end
