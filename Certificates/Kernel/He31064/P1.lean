module

public import Certificates.Kernel.He31064.M
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He31064.CP

open CFSG.KD.He31064

theorem p5 : pOK 40 8 = true := by quickRfl
theorem p6 : pOK 48 8 = true := by quickRfl
theorem p7 : pOK 56 8 = true := by quickRfl
theorem p8 : pOK 64 8 = true := by quickRfl
theorem p9 : pOK 72 6 = true := by quickRfl

end CFSG.KD.He31064.CP

end
