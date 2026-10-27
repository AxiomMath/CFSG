module

public import Certificates.Kernel.OmegaEight.SA3002K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEightMinus

theorem kFiveM0 : allBlk 0 fiveJM 4 = true := by quickRfl
theorem kFiveM1 : allBlk 4 fiveJM 4 = true := by quickRfl
theorem kFiveM2 : allBlk 8 fiveJM 4 = true := by quickRfl
theorem kFiveM3 : allBlk 12 fiveJM 4 = true := by quickRfl
theorem kFiveM4 : allBlk 16 fiveJM 4 = true := by quickRfl
theorem kFiveM5 : allBlk 20 fiveJM 4 = true := by quickRfl
theorem kFiveM6 : allBlk 24 fiveJM 4 = true := by quickRfl
theorem kFiveM7 : allBlk 28 fiveJM 4 = true := by quickRfl
theorem kFiveM8 : allBlk 32 fiveJM 4 = true := by quickRfl

end CertificateChecks.KernelO8

end
