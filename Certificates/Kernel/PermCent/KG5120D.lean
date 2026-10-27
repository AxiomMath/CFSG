module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import CFSG.GH74.KGroups.L33Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5120

open CFSG.GH74.KGroups.L33

theorem kCent3 : cent3C (elemsC QP) = true := by decide +kernel

theorem kSolv : solvC (elemsC QA) (elemsC QP) [48, 24] = true := by decide +kernel

theorem kSolv_neg : solvC (elemsC QA) (elemsC QP) [48] = false := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5120
