module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import CFSG.GH74.KGroups.L33Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5120

open CFSG.GH74.KGroups.L33

theorem kE9 : e9freeC (elemsC QA) = true := by decide +kernel

theorem kE9_neg : ((elemsC QA).all fun τ => bif powOneC τ 2 && !decide (τ = 1) then
    (centL (elemsC QA) τ).all fun X => !powOneC X 3 || decide (X = 1) else true) = false := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5120
