module

public import Certificates.Data.Kernel.O8.S0
public import Certificates.Kernel.OmegaEight.S0Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8

theorem kDistP : distinctOK LPlus = true := by quickRfl
theorem kDistM : distinctOK LMinus = true := by quickRfl
theorem kMtP : mtOK LPlus MTPlus = true := by quickRfl
theorem kMtM : mtOK LMinus MTMinus = true := by quickRfl
theorem kS0P : s0OK LPlus MTPlus UPlus UIPlus TRPlus = true := by quickRfl
theorem kS0M : s0OK LMinus MTMinus UMinus UIMinus TRMinus = true := by quickRfl
theorem kAbelP : abelOK LPlus MTPlus FPlus AMPlus NPlus CIPlus = true := by quickRfl
theorem kAbelM : abelOK LMinus MTMinus FMinus AMMinus NMinus CIMinus = true := by quickRfl

end CertificateChecks.KernelO8

end
