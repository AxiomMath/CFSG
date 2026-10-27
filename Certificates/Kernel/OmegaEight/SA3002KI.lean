module

public import Certificates.Kernel.OmegaEight.SA3002K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEightMinus

theorem kInvolM0 : allBlk 0 (involAtG 36 saCodes yIdxT invWT) 2048 = true := by quickRfl
theorem kInvolM1 : allBlk 2048 (involAtG 36 saCodes yIdxT invWT) 2048 = true := by quickRfl
theorem kInvolM2 : allBlk 4096 (involAtG 36 saCodes yIdxT invWT) 2048 = true := by quickRfl
theorem kInvolM3 : allBlk 6144 (involAtG 36 saCodes yIdxT invWT) 2048 = true := by quickRfl

end CertificateChecks.KernelO8

end
