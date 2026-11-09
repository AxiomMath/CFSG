module

public import Certificates.Data.Kernel.PermCent.B0Twin
import Certificates.Data.Kernel.PermCent.SealPSp43

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.B0T

open CFSG.ComponentClassification.CatFactsSmall.PSp43 Certificates.OmegaB0
  CFSG.Certificates.Kernel.PkEnum.Seal

theorem kClosed : closedC blC = true := by decide +kernel

theorem kSylow : sylowC (elemsC QT0) blC = true := by
  simp only [elemsC, qT0_strong]
  decide +kernel

theorem kVec : vecChk (allVecs ()) (s5l ()) = true := by decide +kernel

theorem kHom : homC phC (allVecs ()) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.B0T
