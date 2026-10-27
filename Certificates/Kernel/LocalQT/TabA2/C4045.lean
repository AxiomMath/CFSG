module

public import Certificates.Kernel.LocalQT.TabA2.K4045
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.TL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.TabA2 CFSG.KS.TabL34
open CFSG.KD.LQT.TA

theorem hd_ok : penumHdK idn R.cnt 241920 R.T R.PL = true := by quickRfl

theorem cnt_ok : Nat.beq R.cnt 241920 = true := by quickRfl

theorem cg_ok : cgK S.T CG (X 2) kC S.cnt = true := by quickRfl

end CFSG.KD.LQT.TL

#kqb_range CFSG.KD.LQT.TL.T CFSG.KD.LQT.TL.ckT 0 315

end
