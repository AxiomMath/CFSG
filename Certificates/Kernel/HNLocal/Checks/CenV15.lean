module

public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNLocalD
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

@[expose] def D15a : List Nat :=
  [271, 463, 1807, 1999, 2831, 3023, 3343, 3535, 4415, 4607, 5951, 6143, 6975, 7167, 7487, 7679]

@[expose] def D15b : List Nat :=
  [9023, 9215, 9535, 9727, 10559, 10751, 12095, 12287, 13071, 13263, 13583, 13775, 14607, 14799,
    16143, 16335]

theorem ceV15 : CFSG.KC.HNLocal.cenVDAt vm PC TG (D15a ++ D15b) (nat_lit 0x0)
    (nat_lit 0xf) (nat_lit 0x4) (nat_lit 0xa) = true := by
  quickRfl

end CFSG.KD.HNLocal

end
