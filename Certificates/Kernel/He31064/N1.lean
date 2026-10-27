module

public import Certificates.Kernel.He31064.M
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He31064.CN

open CFSG.KD.He31064

theorem n2 : nOK 64 32 = true := by quickRfl
theorem n3 : nOK 96 32 = true := by quickRfl

end CFSG.KD.He31064.CN

end
