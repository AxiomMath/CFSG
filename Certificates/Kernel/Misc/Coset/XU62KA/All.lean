module

public import Certificates.Kernel.Misc.Coset.XU62KA.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.XU62K

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 8064) (CFSG.KC.MiscCoset.Act.coverPointOK CFSG.KAct.XU62K.A CFSG.KAct.XU62K.B (nat_lit 5) (nat_lit 8064) CFSG.KAct.XU62K.R CFSG.KAct.XU62K.W) = true := by
  allR_blocks 8

theorem moves : CFSG.KC.MiscCoset.Act.movesOK CFSG.KAct.XU62K.A (Nat.add (nat_lit 5) (nat_lit 5)) CFSG.KAct.XU62K.M = true := by quickRfl

end CFSG.KAct.XU62K

end
