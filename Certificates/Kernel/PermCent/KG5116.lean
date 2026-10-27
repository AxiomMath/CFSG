module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK
public import CFSG.GH74.KGroups.L217Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpCSound

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5116

open CFSG.GH74.KGroups.L217 CFSG.Certificates.Kernel.PkEnum

theorem kQP : schP QP = true ∧ orderV QP = 2448 := by constructor <;> decide +kernel

theorem kQA : schP QA = true ∧ orderV QA = 4896 := by constructor <;> decide +kernel

theorem kOrd : orderIsC (cOf pa) 2 = true ∧ orderIsC (cOf pb) 3 = true ∧
    pairInvC ws (cOf pa) (cOf pb) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem kNorm : normC QP (QA.original.toList.map cOf) (cOf pa) (cOf pb) = true := by
  decide +kernel

theorem kCent : centTrivC (elemsC QA) (cOf pa) (cOf pb) = true := by decide +kernel

theorem kE9 : e9allC (elemsC QA) = true := by decide +kernel

theorem kInner3 : inner3C (elemsC QA) QP = true := by decide +kernel

theorem kSolv : solvC (elemsC QA) (elemsC QP) [16, 18] = true := by decide +kernel

theorem kCl : ((elemsC QP).filter fun x => orderIsC x 2).all
    (fun x => (elemsC QP).any fun g => eq22C g (cOf pa) x g) = true := by
  decide +kernel

theorem kInv : ((elemsC QP).filter fun x => orderIsC x 2).length = 153 := by decide +kernel

theorem kPart : (((elemsC QP).filter fun y => orderIsC y 3).filter fun y =>
    pairInvC ws (cOf pa) y).length = 32 := by
  decide +kernel

theorem kCount : pairCountC (elemsC QP) 2 3 ws = 4896 := by
  rw [pairCount_conj QP (check_certificate_of _ _ _ _ _ kQP.1) 2 3 ws (cOf pa) 32 kCl kPart, kInv]

theorem kNeg : orderIsC (cOf pb) 2 = false ∧ solvC (elemsC QA) (elemsC QP) [16] = false ∧
    centTrivC (elemsC QA) 1 1 = false ∧ ((elemsC QA).all fun g => siftC QP g 0) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5116
