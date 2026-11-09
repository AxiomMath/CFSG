module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK
public import CFSG.GH74.KGroups.A7Inputs
import CFSG.Certificates.Kernel.PermCent.KGrpCSound

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5109

open CFSG.GH74.KGroups.A7 CFSG.Certificates.Kernel.PkEnum

theorem kQP : schP QP = true ∧ orderV QP = 2520 := by constructor <;> decide +kernel

theorem kQA : schP QA = true ∧ orderV QA = 5040 := by constructor <;> decide +kernel

theorem kOrd : orderIsC (cOf pa) 2 = true ∧ orderIsC (cOf pb) 5 = true ∧
    pairInvC ws (cOf pa) (cOf pb) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem kNorm : normC QP (QA.original.toList.map cOf) (cOf pa) (cOf pb) = true := by
  decide +kernel

theorem kCent : centTrivC (elemsC QA) (cOf pa) (cOf pb) = true := by decide +kernel

theorem kInner3 : inner3C (elemsC QA) QP = true := by decide +kernel

theorem kCl : ((elemsC QP).filter fun x => orderIsC x 2).all
    (fun x => (elemsC QP).any fun g => eq22C g (cOf pa) x g) = true := by
  decide +kernel

theorem kInv : ((elemsC QP).filter fun x => orderIsC x 2).length = 105 := by decide +kernel

theorem kPart : (((elemsC QP).filter fun y => orderIsC y 5).filter fun y =>
    pairInvC ws (cOf pa) y).length = 48 := by
  decide +kernel

theorem kCount : pairCountC (elemsC QP) 2 5 ws = 5040 := by
  rw [pairCount_conj QP (check_certificate_of _ _ _ _ _ kQP.1) 2 5 ws (cOf pa) 48 kCl kPart, kInv]

end CFSG.Certificates.Kernel.PkCV.KGrp.K5109
