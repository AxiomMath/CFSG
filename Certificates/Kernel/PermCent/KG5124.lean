
module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import Certificates.Data.Kernel.PermCent.L34Cent
public import CFSG.GH74.KGroups.L34TablesInputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5124

open CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum

theorem kQH : schP QH = true ∧ orderV QH = 768 := by constructor <;> decide +kernel

theorem kX0 : siftC QP (cOf x0) 0 = true ∧ orderIsC (cOf x0) 2 = true := by
  constructor <;> decide +kernel

theorem kHGens : hGens.all (fun g => siftC QA (cOf g) 0 && eq22C (cOf g) (cOf x0) (cOf x0) (cOf g)) =
    true := by
  decide +kernel

theorem kKGens : kGens.all (fun g => siftC QP (cOf g) 0 && eq22C (cOf g) (cOf x0) (cOf x0) (cOf g)) =
    true := by
  decide +kernel

theorem kSq : (elemsC QH).all (fun σ =>
    !(kGens.all fun k => eq22C σ (cOf k) (cOf k) σ) || powOneC σ 2) = true := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5124
