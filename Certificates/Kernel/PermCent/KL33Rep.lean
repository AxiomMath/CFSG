module

public import Certificates.Data.Kernel.PermCent.L33RepTwin
public import CFSG.GH74.KGroups.L33Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L33R.KRep

open CFSG.GH74.KGroups.L33

theorem kOddInner : oddCoreRepC 351 (elemsC QA) (elemsC QP) (cOf PA) = true := by decide +kernel

theorem kGoodInner : goodAtC 100 (elemsC QP) (elemsC QA) (cOf PA) = true := by decide +kernel

theorem kOddOuter : oddCoreRepC 351 (elemsC QA) (elemsC QP) (cOf sg0 ^ 3) = true := by
  decide +kernel

theorem kGoodOuter : goodAtC 100 (elemsC QP) (elemsC QA) (cOf sg0 ^ 3) = true := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.L33R.KRep

end
