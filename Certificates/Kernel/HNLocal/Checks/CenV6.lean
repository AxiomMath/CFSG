module

public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNLocalD
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

@[expose] def D6a : List Nat :=
  [358, 614, 1126, 1894, 2150, 2918, 3430, 3686, 4438, 4694, 5206, 5974, 6230, 6998, 7510, 7766]

@[expose] def D6b : List Nat :=
  [8294, 9062, 9574, 9830, 10598, 10854, 11366, 12134, 12374, 13142, 13654, 13910, 14678, 14934,
    15446, 16214]

theorem ceV6 : CFSG.KC.HNLocal.cenVDAt vm PC TG (D6a ++ D6b) (nat_lit 0x0)
    (nat_lit 0x6) (nat_lit 0x4) (nat_lit 0xa) = true := by
  quickRfl

end CFSG.KD.HNLocal

end
