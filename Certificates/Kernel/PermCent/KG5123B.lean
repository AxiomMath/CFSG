
module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import CFSG.GH74.KGroups.L34AutInputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5123

open CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum

theorem kOrd : orderIsC (cOf PA) 2 = true ∧ orderIsC (cOf PB) 4 = true ∧
    pairInvC ws (cOf PA) (cOf PB) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem kNorm : normC QP (QA.original.toList.map cOf) (cOf PA) (cOf PB) = true := by
  decide +kernel

theorem kInv : ((elemsC QP).filter fun x => orderIsC x 2).length = 315 := by decide +kernel

theorem kConj : ((elemsC QP).filter fun x => orderIsC x 2).all
    (fun x => (elemsC QP).any fun g => eq22C g (cOf PA) x g) = true := by
  decide +kernel

theorem kPart : (((elemsC QP).filter fun y => orderIsC y 4).filter fun y =>
    pairInvC ws (cOf PA) y).length = 768 := by
  decide +kernel

theorem kNeg : orderIsC (cOf PB) 2 = false ∧
    ((elemsC QP).any fun g => eq22C g (cOf PA) (cOf PB) g) = false := by
  constructor <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5123
