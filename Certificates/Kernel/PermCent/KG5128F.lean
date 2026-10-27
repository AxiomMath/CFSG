module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK65
public import CFSG.GH74.KGroups.Sz8Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5128

open CFSG.GH74.KGroups.Sz8 CFSG.Certificates.Kernel.PkEnum

theorem k64 : (centL (elemsC QP) (cOf pa)).length = 64 := by decide +kernel

theorem kSolv_neg : (centL [cOf pa, cOf pb] (cOf pa)).length = 1 := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5128
