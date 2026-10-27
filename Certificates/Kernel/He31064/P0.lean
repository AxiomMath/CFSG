module

public import Certificates.Kernel.He31064.M
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He31064.CP

open CFSG.KD.He31064

theorem p0 : pOK 0 8 = true := by quickRfl
theorem p1 : pOK 8 8 = true := by quickRfl
theorem p2 : pOK 16 8 = true := by quickRfl
theorem p3 : pOK 24 8 = true := by quickRfl
theorem p4 : pOK 32 8 = true := by quickRfl

end CFSG.KD.He31064.CP

end
