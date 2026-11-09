module

public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNLocalD
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

@[expose] def D13a : List Nat :=
  [541, 557, 1053, 1069, 2077, 2093, 3613, 3629, 4637, 4653, 5149, 5165, 6173, 6189, 7709, 7725]

@[expose] def D13b : List Nat :=
  [9181, 9197, 9693, 9709, 10717, 10733, 12253, 12269, 13277, 13293, 13789, 13805, 14813, 14829,
    16349, 16365]

theorem ceV13 : CFSG.KC.HNLocal.cenVDAt vm PC TG (D13a ++ D13b) (nat_lit 0x0)
    (nat_lit 0xd) (nat_lit 0x4) (nat_lit 0xa) = true := by
  quickRfl

end CFSG.KD.HNLocal

end
