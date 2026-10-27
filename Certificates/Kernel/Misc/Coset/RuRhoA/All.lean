module

public import Certificates.Kernel.Misc.Coset.RuRhoA.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.RuRho

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 16240) (CFSG.KC.MiscCoset.Act.coverPointOK CFSG.KAct.RuRho.A CFSG.KAct.RuRho.B (nat_lit 3) (nat_lit 16240) CFSG.KAct.RuRho.R CFSG.KAct.RuRho.W) = true := by
  allR_blocks 150

end CFSG.KAct.RuRho

end
