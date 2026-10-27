module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK
public import CFSG.GH74.KGroups.A6Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5108

open CFSG.GH74.KGroups.A6 CFSG.Certificates.Kernel.PkEnum

theorem kQP : schP QP = true ∧ orderV QP = 360 := by constructor <;> decide +kernel

theorem kQA : schP QA = true ∧ orderV QA = 1440 := by constructor <;> decide +kernel

theorem kOrd : orderIsC (cOf pa) 2 = true ∧ orderIsC (cOf pb) 4 = true ∧
    pairInvC ws (cOf pa) (cOf pb) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem kNorm : normC QP (QA.original.toList.map cOf) (cOf pa) (cOf pb) = true := by
  decide +kernel

theorem kCent : centTrivC (elemsC QA) (cOf pa) (cOf pb) = true := by decide +kernel

theorem kE9 : e9freeC (elemsC QA) = true := by decide +kernel

theorem kInner3 : inner3C (elemsC QA) QP = true := by decide +kernel

theorem kCent3 : cent3C (elemsC QP) = true := by decide +kernel

theorem kSolv : solvC (elemsC QA) (elemsC QP) [8, 10, 24] = true := by decide +kernel

theorem kCount : pairCountC (elemsC QP) 2 4 ws = 1440 := by decide +kernel

theorem kNeg : orderIsC (cOf pb) 2 = false ∧ solvC (elemsC QA) (elemsC QP) [8, 10] = false ∧
    centTrivC (elemsC QA) 1 1 = false ∧ ((elemsC QA).all fun g => siftC QP g 0) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5108
