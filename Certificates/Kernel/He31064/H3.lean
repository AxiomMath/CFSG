module

public import Certificates.Kernel.He31064.M
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He31064.CH

open CFSG.KD.He31064

theorem h12 : hOK 96 8 = true := by quickRfl
theorem h13 : hOK 104 8 = true := by quickRfl
theorem h14 : hOK 112 8 = true := by quickRfl
theorem h15 : hOK 120 8 = true := by quickRfl
theorem h16 : hOK 128 5 = true := by quickRfl

end CFSG.KD.He31064.CH

end
