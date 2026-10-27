module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK65
public import CFSG.GH74.KGroups.Sz8Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5128

open CFSG.GH74.KGroups.Sz8 CFSG.Certificates.Kernel.PkEnum

theorem kCent : centTrivC (elemsC QA) (cOf pa) (cOf pb) = true := by decide +kernel

theorem kCent_neg : centTrivC (elemsC QA) 1 1 = false := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5128
