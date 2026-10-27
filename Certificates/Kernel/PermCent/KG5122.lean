module

public import CFSG.GH74.KGroups.L34Inputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5122

open CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum

theorem kQP21 : schP QP21 = true ∧ orderV QP21 = 20160 := by constructor <;> decide +kernel

theorem kQP : orderV QP = 20160 := by decide +kernel

theorem kBlk : CFSG.GH74.KGroups.blockHom 21 21 (pa, pa') = PA ∧
    CFSG.GH74.KGroups.blockHom 21 21 (pb, pb') = PB := by
  constructor <;> decide +kernel

theorem kNeg : orderV QP21 ≠ 10080 ∧ CFSG.GH74.KGroups.blockHom 21 21 (pb, pb') ≠ PA := by
  constructor <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5122
