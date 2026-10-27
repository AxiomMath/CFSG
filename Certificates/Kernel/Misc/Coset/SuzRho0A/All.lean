module

public import Certificates.Kernel.Misc.Coset.SuzRho0A.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.SuzRho0

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 5346) (CFSG.KC.MiscCoset.Act.coverPointOK CFSG.KAct.SuzRho0.A CFSG.KAct.SuzRho0.B (nat_lit 7) (nat_lit 5346) CFSG.KAct.SuzRho0.R CFSG.KAct.SuzRho0.W) = true := by
  allR_blocks 64

end CFSG.KAct.SuzRho0

end
