module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import CFSG.GH74.KGroups.L33Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpCSound

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5120

open CFSG.GH74.KGroups.L33 CFSG.Certificates.Kernel.PkEnum

theorem kQP13 : schP QP13 = true ∧ orderV QP13 = 5616 := by constructor <;> decide +kernel

theorem kQP : schP QP = true ∧ orderV QP = 5616 := by constructor <;> decide +kernel

theorem kQA : schP QA = true ∧ orderV QA = 11232 := by constructor <;> decide +kernel

theorem kOrd : orderIsC (cOf PA) 2 = true ∧ orderIsC (cOf PB) 3 = true ∧
    pairInvC ws (cOf PA) (cOf PB) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem kNorm : normC QP (QA.original.toList.map cOf) (cOf PA) (cOf PB) = true := by
  decide +kernel

theorem kCent : centTrivC (elemsC QA) (cOf PA) (cOf PB) = true := by decide +kernel

theorem kInner3 : inner3C (elemsC QA) QP = true := by decide +kernel

theorem kBlk : CFSG.GH74.KGroups.blockHom 13 13 (pa, pa') = PA ∧
    CFSG.GH74.KGroups.blockHom 13 13 (pb, pb') = PB := by
  constructor <;> decide +kernel

theorem kCl : ((elemsC QP).filter fun x => orderIsC x 2).all
    (fun x => (elemsC QP).any fun g => eq22C g (cOf PA) x g) = true := by
  decide +kernel

theorem kInv : ((elemsC QP).filter fun x => orderIsC x 2).length = 117 := by decide +kernel

theorem kPart : (((elemsC QP).filter fun y => orderIsC y 3).filter fun y =>
    pairInvC ws (cOf PA) y).length = 96 := by
  decide +kernel

theorem kCount : pairCountC (elemsC QP) 2 3 ws = 11232 := by
  rw [pairCount_conj QP (check_certificate_of _ _ _ _ _ kQP.1) 2 3 ws (cOf PA) 96 kCl kPart, kInv]

theorem kNeg : orderIsC (cOf PB) 2 = false ∧ centTrivC (elemsC QA) 1 1 = false ∧
    ((elemsC QA).all fun g => siftC QP g 0) = false ∧
    CFSG.GH74.KGroups.blockHom 13 13 (pb, pb') ≠ PA := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5120
