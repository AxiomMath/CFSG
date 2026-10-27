module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK65
public import CFSG.GH74.KGroups.Sz8Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5128

open CFSG.GH74.KGroups.Sz8 CFSG.Certificates.Kernel.PkEnum

theorem kQP : schP QP = true ∧ orderV QP = 29120 := by constructor <;> decide +kernel

theorem kQA : schP QA = true ∧ orderV QA = 87360 := by constructor <;> decide +kernel

theorem kOrd : orderIsC (cOf pa) 2 = true ∧ orderIsC (cOf pb) 4 = true ∧
    pairInvC ws (cOf pa) (cOf pb) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem kNorm : normC QP (QA.original.toList.map cOf) (cOf pa) (cOf pb) = true := by
  decide +kernel

theorem kNegA : orderV QA ≠ 29120 ∧ orderIsC (cOf pb) 2 = false ∧ siftC QP (cOf sg0) 0 = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5128
