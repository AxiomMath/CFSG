module

public import Certificates.Kernel.Misc.Coset.XT46W.Data
public import Certificates.Kernel.Misc.T46Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.XT46W

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 693) (CFSG.KC.MiscCoset.T46W.pointK CFSG.KAct.XT46W.A CFSG.KD.Misc.T46.GP CFSG.KAct.XT46W.R CFSG.KAct.XT46W.XW [30, 33, 16, 12, 9, 39, 39] CFSG.KAct.XT46W.YW [41, 46, 21, 23, 36]) = true := by
  allR_blocks 16

end CFSG.KAct.XT46W

end
