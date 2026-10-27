module

public import Certificates.Data.Kernel.PermCent.L33Twin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L33T

open CFSG.GH74.KGroups.L33

theorem k441621 : (elemsC QA).length = 11232 ∧ (elemsC QA).countP innerC = 117 ∧
    (elemsC QA).countP outerC = 234 ∧ (elemsC QA).countP centKC = 48 ∧
    (elemsC QA).countP centPC = 24 ∧ (elemsC QA).all norm1C = true ∧
    (elemsC QA).all norm2C = true := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.L33T
