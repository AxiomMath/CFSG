module

public import Certificates.Data.Kernel.PermCent.L216Census

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L216C.K6128

open CFSG.GH74.Uniqueness.SU.K.R4.L216M CFSG.Certificates.Kernel.PkCV.KGrp

theorem kB0 : clsBlk 2040 0 = true := by decide +kernel

theorem kB1 : clsBlk 2040 1 = true := by decide +kernel

theorem kB2 : clsBlk 2040 2 = true := by decide +kernel

theorem kB3 : clsBlk 2040 3 = true := by decide +kernel

theorem kB4 : clsBlk 2040 4 = true := by decide +kernel

theorem kB5 : clsBlk 2040 5 = true := by decide +kernel

theorem kB6 : clsBlk 2040 6 = true := by decide +kernel

theorem kB7 : clsBlk 2040 7 = true := by decide +kernel

theorem kTl : clsOK ((elemsC QA).drop (8 * 2040)) (clsV r1) (clsV r2) = true := by decide +kernel

theorem kC1 : (centL (elemsC QP) r1).length = 16 := by decide +kernel

theorem kC2 : (centL (elemsC QP) r2).length = 60 := by decide +kernel

theorem kM : memN r1.1 ((elemsC QP).map Subtype.val) = true ∧
    memN r2.1 ((elemsC QP).map Subtype.val) = false := by
  constructor <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.L216C.K6128

end
