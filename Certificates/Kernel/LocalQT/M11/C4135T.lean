module

public import Certificates.Kernel.LocalQT.M11.C4135
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4135

open CFSG.KC.LQT.M CFSG.KD.LQT.M11

theorem t0 : tripL c0 LI = true := by quickRfl
theorem t1 : tripL c1 LI = true := by quickRfl
theorem t2 : tripL c2 LI = true := by quickRfl
theorem t3 : tripL c3 LI = true := by quickRfl
theorem t4 : tripL c4 LI = true := by quickRfl
theorem t5 : tripL c5 LI = true := by quickRfl
theorem t6 : tripL c6 LI = true := by quickRfl
theorem t7 : tripL c7 LI = true := by quickRfl
theorem t8 : tripL c8 LI = true := by quickRfl
theorem t9 : tripL c9 LI = true := by quickRfl
theorem t10 : tripL c10 LI = true := by quickRfl
theorem ht : tripL LI LI = true := (tripL_append_true (tripL_append_true (tripL_append_true (tripL_append_true (tripL_append_true (tripL_append_true (tripL_append_true (tripL_append_true (tripL_append_true (tripL_append_true t0 t1) t2) t3) t4) t5) t6) t7) t8) t9) t10)

end CFSG.KD.LQT.C4135

end
