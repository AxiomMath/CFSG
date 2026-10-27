module

public import Certificates.Kernel.Sp4Ov.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.Sp4Ov

theorem ch7138_elems : elemsOK D.spM = true := by quickRfl

theorem ch7138_g5 : ((getN D.ov5 0).gens == [58242]) = true := by quickRfl

theorem ch7138_g9 : ((getN D.ov9 0).gens == [34369, 37928]) = true := by quickRfl

theorem ch7138_ov5 : ovK D.spM D.ov5 = true := by quickRfl

theorem ch7138_ov9 : ovK D.spM D.ov9 = true := by quickRfl

end CFSG.KD.Sp4Ov

end
