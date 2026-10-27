module

public import Certificates.Kernel.He31064.M
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He31064.CH

open CFSG.KD.He31064

theorem h8 : hOK 64 8 = true := by quickRfl
theorem h9 : hOK 72 8 = true := by quickRfl
theorem h10 : hOK 80 8 = true := by quickRfl
theorem h11 : hOK 88 8 = true := by quickRfl

end CFSG.KD.He31064.CH

end
