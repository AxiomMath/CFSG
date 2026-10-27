module

public import Certificates.Data.Kernel.PermCent.KGrpC3
public import CFSG.GH74.KGroups.A6Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5003

open CFSG.GH74.KGroups.A6

theorem k5003 : q8c2freeC (elemsC QA) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5003
