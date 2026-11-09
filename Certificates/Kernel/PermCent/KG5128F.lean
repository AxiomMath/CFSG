module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK65
public import CFSG.GH74.KGroups.Sz8Inputs
import Certificates.Data.Kernel.PermCent.SealSz8

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5128

open CFSG.GH74.KGroups.Sz8 CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.PkEnum.Seal

theorem k64 : (centL (elemsC QP) (cOf pa)).length = 64 := by
  simp only [elemsC, sz8QP_strong]
  decide +kernel

theorem kSolv_neg : (centL [cOf pa, cOf pb] (cOf pa)).length = 1 := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5128
