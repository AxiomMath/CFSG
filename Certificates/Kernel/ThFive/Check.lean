module

public import Certificates.Data.Kernel.ThFive.Check
public import Certificates.Kernel.ThFive.Data
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.ThFive

open CFSG.KC.ThFive

theorem chk_ok : chk ThS.c ThS.rm ThS.ONE (ThS.RBf 1) (ThS.RBf 2) S.P1 S.P2 S.P3 S.O1 S.O2 S.O3 = true := by
  quickRfl

end CFSG.KD.ThFive

end
