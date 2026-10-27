module

public import Certificates.Data.Kernel.PermCent.GoodC
public import CFSG.GH74.KGroups.L33Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K9741G

open CFSG.Certificates.Kernel.PkCV.Good CFSG.GH74.KGroups.L33

theorem k9741 : goodC 100 (elemsC QP) = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K9741G
