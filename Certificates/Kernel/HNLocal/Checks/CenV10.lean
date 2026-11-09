module

public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNLocalD
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

@[expose] def D10a : List Nat :=
  [442, 698, 1210, 1978, 2234, 3002, 3514, 3770, 4490, 4746, 5258, 6026, 6282, 7050, 7562, 7818]

@[expose] def D10b : List Nat :=
  [8378, 9146, 9658, 9914, 10682, 10938, 11450, 12218, 12426, 13194, 13706, 13962, 14730, 14986,
    15498, 16266]

theorem ceV10 : CFSG.KC.HNLocal.cenVDAt vm PC TG (D10a ++ D10b) (nat_lit 0x0)
    (nat_lit 0xa) (nat_lit 0x4) (nat_lit 0xa) = true := by
  quickRfl

end CFSG.KD.HNLocal

end
