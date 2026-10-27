module

public import CFSG.Quasithin.H13.KGFactT3J4KInputs
public import Certificates.Kernel.M24Dc.Idx3
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.M24Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H13.KGT3J4

theorem t3j4K : T3J4LatK := by
  unfold T3J4LatK t3yLab t3yTab
  rw [wordTabA_eq_L, codeSetAct_eq, delta_eqK]
  exact of_decide_eq_true (by quickRfl)

end CFSG.KD.M24Dc

end
