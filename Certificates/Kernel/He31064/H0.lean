module

public import Certificates.Kernel.He31064.M
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He31064.CH

open CFSG.KD.He31064

theorem h0 : hOK 0 8 = true := by quickRfl
theorem h1 : hOK 8 8 = true := by quickRfl
theorem h2 : hOK 16 8 = true := by quickRfl
theorem h3 : hOK 24 8 = true := by quickRfl

end CFSG.KD.He31064.CH

end
