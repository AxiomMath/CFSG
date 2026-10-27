
module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import CFSG.GH74.KGroups.L34AutInputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5123

open CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum

theorem kQA : schP QA = true ∧ orderV QA = 241920 := by constructor <;> decide +kernel

theorem kCent : centTrivC (elemsC QA) (cOf PA) (cOf PB) = true := by decide +kernel

theorem kQA_neg : orderV QA ≠ 120960 := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5123
