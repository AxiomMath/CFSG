module

public import Certificates.Data.Kernel.PermCent.B0Twin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.B0T

open CFSG.ComponentClassification.CatFactsSmall.PSp43 Certificates.OmegaB0

theorem kAct : actC (elemsC QP45) (elemsC QA45) ((bl ()).map cOf) phC blC (allVecs ()) (s5l ()) =
    true := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.B0T
