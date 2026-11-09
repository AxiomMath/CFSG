module

public import Certificates.Data.Kernel.PermCent.L27Twin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L27T

open CFSG.GH74.KGroups.L27 Equiv

theorem kNormA : siftC QP (cOf sg0 * cOf pa * (cOf sg0)⁻¹) 0 = true := by decide +kernel

theorem kNormB : siftC QP (cOf sg0 * cOf pb * (cOf sg0)⁻¹) 0 = true := by decide +kernel

theorem kInvA : (elemsC QA).all (fun y => !decide (y * cOf pa = cOf pa * y) ||
    decide (y ^ 16 = 1)) = true := by
  decide +kernel

theorem kInvB : (elemsC QP).all (fun x => !decide (x * x = 1) || decide (x = 1) ||
    (elemsC QP).any fun g => decide (g * cOf pa * g⁻¹ = x)) = true := by
  decide +kernel

theorem kOuter : outerC = true := by decide +kernel

theorem kA5Inv : ∀ x y : Perm (Fin 5), Perm.sign x = 1 → x * x = 1 → x ≠ 1 →
    y * x = x * y → y ^ 16 = 1 := by
  decide +kernel

theorem kA5Outer : CFSG.ComponentClassification.GrSLit.L34Facts.a5OuterOK = true := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.L27T
