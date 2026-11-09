module

public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNLocalD
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

@[expose] def D5a : List Nat :=
  [901, 949, 1413, 1461, 2437, 2485, 3973, 4021, 4997, 5045, 5509, 5557, 6533, 6581, 8069, 8117]

@[expose] def D5b : List Nat :=
  [8261, 8309, 9797, 9845, 10821, 10869, 11333, 11381, 12357, 12405, 13893, 13941, 14917, 14965,
    15429, 15477]

@[expose] def D5 : List Nat := D5a ++ D5b

theorem ceV5 : CFSG.KC.HNLocal.cenVDAt vm PC TG D5 (nat_lit 0x0)
    (nat_lit 0x5) (nat_lit 0x4) (nat_lit 0xa) = true := by
  quickRfl

end CFSG.KD.HNLocal

end
