module

public import Certificates.Data.Kernel.PermCent.U33Twin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.U33T

open CFSG.GH74.KGroups.U33

theorem k7137 : (cOf pa * cOf pb) ^ 7 = 1 ∧ cOf pa * cOf pb ≠ 1 ∧
    ((elemsC QP).filter fun g => (List.range 7).any fun i =>
      decide (g * (cOf pa * cOf pb) * g⁻¹ = (cOf pa * cOf pb) ^ i)).length = 21 := by
  decide +kernel

theorem kCenter : centerC = true := by decide +kernel

theorem kExp : expC = true := by decide +kernel

theorem kF1 : f1C (elemsC QP) (invsOfC (elemsC QP)) = true := by decide +kernel

theorem kF3 : f3C (invsOfC (elemsC QP)) (o3OfC (elemsC QP)) = true := by decide +kernel

theorem kX5 : x5C (elemsC QP) (invsOfC (elemsC QP)) (o3OfC (elemsC QP)) = true := by
  decide +kernel

theorem kT0 : t0C = true := by decide +kernel

theorem kZ : zC = true := by decide +kernel

theorem kC : cC = true := by decide +kernel

theorem kE1 : e1C = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.U33T
