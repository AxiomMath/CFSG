module

public import Certificates.Data.Kernel.PermCent.B0Twin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.B0T

open CFSG.ComponentClassification.CatFactsSmall.PSp43 Certificates.OmegaB0

theorem kCent : centC (elemsC QA45) blC = true := by decide +kernel

theorem kClass : classC (elemsC QP45) phC (allVecs ()) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.B0T
