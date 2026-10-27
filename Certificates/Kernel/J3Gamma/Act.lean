module

public import Certificates.Kernel.J3Gamma.ActData
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.J3Gamma

open CFSG.KC.MiscCoset.Act

theorem all : allR (nat_lit 0) (nat_lit 5832)
    (pointOK CFSG.KAct.J3Gamma.A (nat_lit 6) (nat_lit 5832) CFSG.KAct.J3Gamma.R) = true := by
  allR_blocks 32

theorem down : allR (nat_lit 1) (nat_lit 5831)
    (downAt CFSG.KAct.J3Gamma.A (Nat.add 6 6) (Nat.add 6 6)) = true := by
  quickRfl

theorem eq : fixAll CFSG.KAct.J3Gamma.A (Nat.add 6 6) CFSG.KAct.J3Gamma.EQ = true := by
  quickRfl

theorem mv : movesOK CFSG.KAct.J3Gamma.A (Nat.add 6 6) CFSG.KAct.J3Gamma.MV = true := by
  quickRfl

end CFSG.KAct.J3Gamma

end
