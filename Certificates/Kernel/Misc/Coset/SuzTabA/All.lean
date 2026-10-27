module

public import Certificates.Kernel.Misc.Coset.SuzTabA.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.SuzTab

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 1782) (CFSG.KC.MiscCoset.Act.pointOK CFSG.KAct.SuzTab.A (nat_lit 9) (nat_lit 1782) CFSG.KAct.SuzTab.rels) = true := by
  allR_blocks 40

end CFSG.KAct.SuzTab

end
