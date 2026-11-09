module

public import Certificates.Data.Kernel.PermCent.L33Twin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L33T

open CFSG.GH74.KGroups.L33

theorem kLen : (elemsC QA).length = 11232 := by
  decide +kernel

theorem kInner : (elemsC QA).countP innerC = 117 := by
  decide +kernel

theorem kOuter : (elemsC QA).countP outerC = 234 := by
  decide +kernel

theorem kCentK : (elemsC QA).countP centKC = 48 := by
  decide +kernel

theorem kCentP : (elemsC QA).countP centPC = 24 := by
  decide +kernel

theorem kNorm1 : (elemsC QA).all norm1C = true := by
  decide +kernel

theorem kNorm2 : (elemsC QA).all norm2C = true := by
  decide +kernel

theorem k441621 : (elemsC QA).length = 11232 ∧ (elemsC QA).countP innerC = 117 ∧
    (elemsC QA).countP outerC = 234 ∧ (elemsC QA).countP centKC = 48 ∧
    (elemsC QA).countP centPC = 24 ∧ (elemsC QA).all norm1C = true ∧
    (elemsC QA).all norm2C = true :=
  ⟨kLen, kInner, kOuter, kCentK, kCentP, kNorm1, kNorm2⟩

end CFSG.Certificates.Kernel.PkCV.L33T
