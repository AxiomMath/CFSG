module

public import Certificates.Data.Kernel.PermCent.SmallF3Twin
public import CFSG.GH74.KGroups.L33Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.SmallF3T.K8040

open CFSG.GH74.KGroups.L33

theorem k8040 : fourGenC (elemsC QA) (elemsC QP) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.SmallF3T.K8040

end
