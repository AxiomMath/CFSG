module

public import Certificates.Kernel.He31064.M
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He31064.CH

open CFSG.KD.He31064

theorem h4 : hOK 32 8 = true := by quickRfl
theorem h5 : hOK 40 8 = true := by quickRfl
theorem h6 : hOK 48 8 = true := by quickRfl
theorem h7 : hOK 56 8 = true := by quickRfl

end CFSG.KD.He31064.CH

end
