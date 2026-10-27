module

public import Certificates.Data.Kernel.PermCent.KGrpC2
public import Certificates.Data.Kernel.PermCent.KGrpC
public import CFSG.GH74.KGroups.U33Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5098C

open CFSG.GH74.KGroups.U33

theorem kInv : ((elemsC QA).filter fun τ => powOneC τ 2 && !decide (τ = 1)).length = 315 := by
  decide +kernel

theorem kP : (elemsC QP).length = 6048 := by decide +kernel

theorem kU : (centL (elemsC QP) (cOf pu)).length = 96 ∧
    oddCoreAtC 189 (centL (elemsC QA) (cOf pu)) (centL (elemsC QP) (cOf pu)) = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

theorem kT : (centL (elemsC QP) (cOf pt2)).length = 24 ∧
    oddCoreAtC 189 (centL (elemsC QA) (cOf pt2)) (centL (elemsC QP) (cOf pt2)) = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

theorem kRep : siftC QA (cOf pu) 0 = true ∧ siftC QA (cOf pt2) 0 = true ∧
    siftC QP (cOf pu) 0 = true ∧ siftC QP (cOf pt2) 0 = false ∧
    (powOneC (cOf pu) 2 && !decide (cOf pu = 1)) = true ∧
    (powOneC (cOf pt2) 2 && !decide (cOf pt2 = 1)) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5098C

end
