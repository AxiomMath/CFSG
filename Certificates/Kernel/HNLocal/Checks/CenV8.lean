module

public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNLocalD
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

@[expose] def D8a : List Nat :=
  [248, 264, 600, 616, 1112, 1128, 1784, 1800, 2136, 2152, 2808, 2824, 3320, 3336, 3672, 3688,
    4344, 4360, 4696, 4712, 5208, 5224]

@[expose] def D8b : List Nat :=
  [5880, 5896, 6232, 6248, 6904, 6920, 7416, 7432, 7768, 7784, 8600, 8616, 8904, 9016, 9416, 9528,
    10136, 10152, 10440, 10552, 11160]

@[expose] def D8c : List Nat :=
  [11176, 11672, 11688, 11976, 12088, 12696, 12712, 13000, 13112, 13512, 13624, 14232, 14248,
    14536, 14648, 15256, 15272, 15768, 15784, 16072, 16184]

theorem ceV8 : CFSG.KC.HNLocal.cenVDAt vm PC TG (D8a ++ (D8b ++ D8c)) (nat_lit 0x0)
    (nat_lit 0x8) (nat_lit 0x4) (nat_lit 0xa) = true := by
  quickRfl

end CFSG.KD.HNLocal

end
