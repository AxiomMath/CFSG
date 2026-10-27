module

public import Certificates.Kernel.OmegaEight.SA3002K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEightMinus

theorem kRgM0 : allBlk 0 rgJM 8 = true := by quickRfl
theorem kRgM1 : allBlk 8 rgJM 8 = true := by quickRfl
theorem kRgM2 : allBlk 16 rgJM 8 = true := by quickRfl
theorem kRgM3 : allBlk 24 rgJM 8 = true := by quickRfl
theorem kRgM4 : allBlk 32 rgJM 4 = true := by quickRfl

end CertificateChecks.KernelO8

end
