module

public import Certificates.Kernel.LocalQT.TwoB.C4150K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.TB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

theorem base_ok : bAnd(szOK 3850 12, bAnd(canonK 3850 12 (mask 12) (3850 * 12) idK,
    bAnd(CFSG.KS.Prim.idK 3850 12 (mask 12),
    bAnd(allN 4 (fun j => canonK 3850 12 (mask 12) (3850 * 12) (cC j)),
    bAnd(allN 4 (fun j => canonK 3850 12 (mask 12) (3850 * 12) (cCI j)),
    bAnd(allN 2 (fun j => Nat.beq (Y.G j) idK),
    bAnd(Nat.beq (Y.GI 0) (wfoldK 3850 12 (mask 12) cL [4, 2, 1, 4] idK),
    bAnd(Nat.beq (Y.GI 1) (wfoldK 3850 12 (mask 12) cL [3, 3] idK),
    bAnd(allN 2 (fun j => invEqK 3850 12 (mask 12) (3850 * 12) (Y.GI j) (YI j)),
    bAnd(allN 2 (fun j => canonK 3850 12 (mask 12) (3850 * 12) (YI j)),
    bAnd(penumHdK idK Y.cnt 400 Y.T Y.PL, Nat.beq Y.cnt 360))))))))))) = true := by
  quickRfl

end CFSG.KD.LQT.TB

#kqb_range CFSG.KD.LQT.TB.E CFSG.KD.LQT.TB.ckE 0 90

end
