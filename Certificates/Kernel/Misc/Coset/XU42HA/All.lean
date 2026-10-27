module

public import Certificates.Kernel.Misc.Coset.XU42HA.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.XU42H

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 4320) (CFSG.KC.MiscCoset.Act.coverPointOK CFSG.KAct.XU42H.A CFSG.KAct.XU42H.B (nat_lit 2) (nat_lit 4320) CFSG.KAct.XU42H.R CFSG.KAct.XU42H.W) = true := by
  allR_blocks 16

theorem cyc0 : CFSG.KC.MiscCoset.Act.cycleOK CFSG.KAct.XU42H.A (Nat.add (nat_lit 2) (nat_lit 2)) CFSG.KAct.XU42H.C0 (nat_lit 2) = true := by quickRfl

end CFSG.KAct.XU42H

end
