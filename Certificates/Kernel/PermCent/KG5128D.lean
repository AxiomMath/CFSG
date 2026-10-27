module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.SmallK65
public import CFSG.GH74.KGroups.Sz8Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5128

open CFSG.GH74.KGroups.Sz8 CFSG.Certificates.Kernel.PkEnum

theorem kInv : ((elemsC QP).filter fun x => orderIsC x 2).length = 455 := by decide +kernel

theorem kConj : ((elemsC QP).filter fun x => orderIsC x 2).all
    (fun x => (elemsC QP).any fun g => eq22C g (cOf pa) x g) = true := by
  decide +kernel

theorem kPart : (((elemsC QP).filter fun y => orderIsC y 4).filter fun y =>
    pairInvC ws (cOf pa) y).length = 192 := by
  decide +kernel

theorem kNegD : ((elemsC QP).any fun g => eq22C g (cOf pa) (cOf pb) g) = false := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5128
