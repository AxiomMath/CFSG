module

public import Certificates.Data.Kernel.PermCent.B0Twin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.B0T

open CFSG.ComponentClassification.CatFactsSmall.PSp43 Certificates.OmegaB0

theorem kClosed : closedC blC = true := by decide +kernel

theorem kSylow : sylowC (elemsC QT0) blC = true := by decide +kernel

theorem kVec : vecChk (allVecs ()) (s5l ()) = true := by decide +kernel

theorem kHom : homC phC (allVecs ()) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.B0T
