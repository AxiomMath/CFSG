module

public import Certificates.Kernel.Misc.Coset.SuzRhoJ2A.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.SuzRhoJ2

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 200) (CFSG.KC.MiscCoset.Act.pointOK CFSG.KAct.SuzRhoJ2.A (nat_lit 5) (nat_lit 200) CFSG.KAct.SuzRhoJ2.rels) = true := by
  allR_blocks 25

end CFSG.KAct.SuzRhoJ2

end
