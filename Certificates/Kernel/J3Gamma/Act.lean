module

public import Certificates.Kernel.J3Gamma.ActData
public import Certificates.Kernel.Misc.Coset.ActBlocks
public import CFSG.Certificates.Kernel.Misc.Coset.ActLeft
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.J3Gamma

open CFSG.KC.MiscCoset.Act

theorem all : allR (nat_lit 0) (nat_lit 5832)
    (leftPointOK CFSG.KAct.J3Gamma.A CFSG.KAct.J3Gamma.S CFSG.KAct.J3Gamma.P (nat_lit 6)
      (nat_lit 5832) (nat_lit 2)) = true := by
  allR_blocks 32

theorem rel0 : relsAt CFSG.KAct.J3Gamma.A (Nat.add 6 6) CFSG.KAct.J3Gamma.R 0 = true := by
  quickRfl

theorem down : allR (nat_lit 1) (nat_lit 5831)
    (downAt CFSG.KAct.J3Gamma.A (Nat.add 6 6) (Nat.add 6 6)) = true := by
  quickRfl

theorem eq : fixAll CFSG.KAct.J3Gamma.A (Nat.add 6 6) CFSG.KAct.J3Gamma.EQ = true := by
  quickRfl

theorem mv : movesOK CFSG.KAct.J3Gamma.A (Nat.add 6 6) CFSG.KAct.J3Gamma.MV = true := by
  quickRfl

end CFSG.KAct.J3Gamma

end
