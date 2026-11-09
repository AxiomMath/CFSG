module

public import Certificates.Data.Kernel.PermCent.SmallF3Twin
import Certificates.Kernel.PermCent.C6Hoist

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.SmallF3T.K442271

open CFSG.GH74.KGroups.U33

theorem k442271 : c6freeC (elemsC QA) (elemsC QP) = true := by
  rw [c6freeC_eq]
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.SmallF3T.K442271

end
