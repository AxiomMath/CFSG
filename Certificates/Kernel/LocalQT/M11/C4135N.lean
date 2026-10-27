module

public import Certificates.Kernel.LocalQT.M11.C4135
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4135

open CFSG.KC.LQT.M CFSG.KD.LQT.M11

theorem b0 : cntOK c0 LF 720 = true := by quickRfl
theorem b1 : cntOK c1 LF 720 = true := by quickRfl
theorem b2 : cntOK c2 LF 720 = true := by quickRfl
theorem b3 : cntOK c3 LF 720 = true := by quickRfl
theorem b4 : cntOK c4 LF 720 = true := by quickRfl
theorem b5 : cntOK c5 LF 720 = true := by quickRfl
theorem b6 : cntOK c6 LF 720 = true := by quickRfl
theorem b7 : cntOK c7 LF 720 = true := by quickRfl
theorem b8 : cntOK c8 LF 720 = true := by quickRfl
theorem b9 : cntOK c9 LF 720 = true := by quickRfl
theorem b10 : cntOK c10 LF 720 = true := by quickRfl
theorem hc0 : cntOK (c0 ++ c1 ++ c2 ++ c3 ++ c4 ++ c5 ++ c6 ++ c7 ++ c8 ++ c9 ++ c10) LF (720 + 720 + 720 + 720 + 720 + 720 + 720 + 720 + 720 + 720 + 720) = true :=
  (cntOK_append (cntOK_append (cntOK_append (cntOK_append (cntOK_append (cntOK_append (cntOK_append (cntOK_append (cntOK_append (cntOK_append b0 b1) b2) b3) b4) b5) b6) b7) b8) b9) b10)
theorem hc : cntOK LI LF 7920 = true := by
  have h := hc0
  simp only [Nat.reduceAdd] at h
  exact h

end CFSG.KD.LQT.C4135

end
