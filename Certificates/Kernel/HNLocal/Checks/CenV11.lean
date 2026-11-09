module

public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNLocalD
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

@[expose] def D11a : List Nat :=
  [331, 955, 1467, 1867, 2491, 2891, 3403, 4027, 4475, 5003, 5515, 6011, 6539, 7035, 7547, 8075]

@[expose] def D11b : List Nat :=
  [8587, 9083, 9595, 10123, 10619, 11147, 11659, 12155, 12731, 13131, 13643, 14267, 14667, 15291,
    15803, 16203]

theorem ceV11 : CFSG.KC.HNLocal.cenVDAt vm PC TG (D11a ++ D11b) (nat_lit 0x0)
    (nat_lit 0xb) (nat_lit 0x4) (nat_lit 0xa) = true := by
  quickRfl

end CFSG.KD.HNLocal

end
