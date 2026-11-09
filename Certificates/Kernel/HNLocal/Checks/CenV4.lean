module

public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNLocalD
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

@[expose] def D4a : List Nat :=
  [388, 884, 1396, 1924, 2420, 2948, 3460, 3956, 4308, 4324, 4532, 4628, 4644, 4932, 5140, 5156,
    5444, 5844, 5860, 6068, 6164, 6180]

@[expose] def D4b : List Nat :=
  [6468, 6868, 6884, 7092, 7380, 7396, 7604, 7700, 7716, 8004, 8212, 8228, 8516, 8916, 8932, 9140,
    9428, 9444, 9652, 9748, 9764]

@[expose] def D4c : List Nat :=
  [10052, 10452, 10468, 10676, 10772, 10788, 11076, 11284, 11300, 11588, 11988, 12004, 12212,
    12660, 13188, 13700, 14196, 14724, 15220, 15732, 16260]

theorem ceV4 : CFSG.KC.HNLocal.cenVDAt vm PC TG (D4a ++ (D4b ++ D4c)) (nat_lit 0x0)
    (nat_lit 0x4) (nat_lit 0x4) (nat_lit 0xa) = true := by
  quickRfl

end CFSG.KD.HNLocal

end
