module

public import Certificates.Data.Kernel.PermCent.L216Twin
import CFSG.Certificates.Kernel.PermCent.KGrpCSound

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5137

open CFSG.GH74.Uniqueness.SU.K.R4.L216M CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.PkCV.L216T

theorem kQP : schP QP = true ∧ orderV QP = 4080 := by constructor <;> decide +kernel

theorem kQA : schP QA = true ∧ orderV QA = 16320 := by constructor <;> decide +kernel

theorem kOrd : orderIsC (cOf pa) 2 = true ∧ orderIsC (cOf pb) 3 = true ∧
    pairInvC ws (cOf pa) (cOf pb) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem kNorm : normC QP (QA.original.toList.map cOf) (cOf pa) (cOf pb) = true := by
  decide +kernel

theorem kCent : centTrivC (elemsC QA) (cOf pa) (cOf pb) = true := by decide +kernel

theorem kE4 : e4C = true := by decide +kernel

theorem kCl : ((elemsC QP).filter fun x => orderIsC x 2).all
    (fun x => (elemsC QP).any fun g => eq22C g (cOf pa) x g) = true := by
  decide +kernel

theorem kInv : ((elemsC QP).filter fun x => orderIsC x 2).length = 255 := by decide +kernel

theorem kPart : (((elemsC QP).filter fun y => orderIsC y 3).filter fun y =>
    pairInvC ws (cOf pa) y).length = 64 := by
  decide +kernel

theorem kCount : pairCountC (elemsC QP) 2 3 ws = 16320 := by
  rw [pairCount_conj QP (check_certificate_of _ _ _ _ _ kQP.1) 2 3 ws (cOf pa) 64 kCl kPart, kInv]

end CFSG.Certificates.Kernel.PkCV.KGrp.K5137
