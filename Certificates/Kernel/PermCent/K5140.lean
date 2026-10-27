
module

public import Certificates.Data.Kernel.PermCent.L34ModelTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L34Mod

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkCV

theorem kS : sC.length = 64 := by decide +kernel

theorem kScan : modelC (elemsC QA) (elemsC QP) sC gS = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.L34Mod

end
