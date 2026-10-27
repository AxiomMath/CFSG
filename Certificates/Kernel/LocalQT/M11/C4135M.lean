module

public import Certificates.Kernel.LocalQT.M11.C4135
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4135

open CFSG.KC.LQT.M CFSG.KD.LQT.M11

theorem m0 : m4135 R1 R2 R3 R4 LI LF 0 = true := by quickRfl
theorem m1 : m4135 R1 R2 R3 R4 LI LF 1 = true := by quickRfl
theorem m2 : m4135 R1 R2 R3 R4 LI LF 2 = true := by quickRfl
theorem m3 : m4135 R1 R2 R3 R4 LI LF 3 = true := by quickRfl
theorem m4 : m4135 R1 R2 R3 R4 LI LF 4 = true := by quickRfl
theorem m5 : m4135 R1 R2 R3 R4 LI LF 5 = true := by quickRfl
theorem m6 : m4135 R1 R2 R3 R4 LI LF 6 = true := by quickRfl
theorem m7 : m4135 R1 R2 R3 R4 LI LF 7 = true := by quickRfl
theorem m8 : m4135 R1 R2 R3 R4 LI LF 8 = true := by quickRfl
theorem m9 : m4135 R1 R2 R3 R4 LI LF 9 = true := by quickRfl
theorem m10 : m4135 R1 R2 R3 R4 LI LF 10 = true := by quickRfl
theorem hm : ∀ a < 11, m4135 R1 R2 R3 R4 LI LF a = true :=
  forall_lt_11 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10

end CFSG.KD.LQT.C4135

end
