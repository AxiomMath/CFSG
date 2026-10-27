module

public import Certificates.Kernel.Misc.Coset.XTitsPA.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.XTitsP

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 1755) (CFSG.KC.MiscCoset.Act.pointOK CFSG.KAct.XTitsP.A (nat_lit 5) (nat_lit 1755) CFSG.KAct.XTitsP.rels) = true := by
  allR_blocks 16

end CFSG.KAct.XTitsP

end
