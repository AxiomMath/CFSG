module

public import Certificates.Kernel.PhanA3.ActData
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.PhanA3

open CFSG.KC.MiscCoset.Act

theorem all : allR (nat_lit 0) (nat_lit 19440)
    (pointOK CFSG.KAct.PhanA3.A (nat_lit 6) (nat_lit 19440) CFSG.KAct.PhanA3.R) = true := by
  allR_blocks 32

theorem cycles : cycAll CFSG.KAct.PhanA3.A (Nat.add 6 6) CFSG.KAct.PhanA3.KW 3 = true := by
  quickRfl

end CFSG.KAct.PhanA3

end
