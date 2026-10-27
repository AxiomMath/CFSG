module

public import Certificates.Kernel.LocalComp.M12Over.S1
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Over

theorem c6_0 : cK 6 0 = true := by quickRfl
theorem c6_1 : cK 6 1 = true := by quickRfl
theorem c6_2 : cK 6 2 = true := by quickRfl
theorem c6_3 : cK 6 3 = true := by quickRfl
theorem c6_4 : cK 6 4 = true := by quickRfl
theorem c6_5 : cK 6 5 = true := by quickRfl
theorem c6_6 : cK 6 6 = true := by quickRfl
theorem c6_7 : cK 6 7 = true := by quickRfl
theorem c6_8 : cK 6 8 = true := by quickRfl
theorem c6_9 : cK 6 9 = true := by quickRfl
theorem c6_10 : cK 6 10 = true := by quickRfl

theorem s6 : ∀ k₁ < 11, cK 6 k₁ = true := by
  intro k₁ hk
  interval_cases k₁
  exacts [c6_0, c6_1, c6_2, c6_3, c6_4, c6_5, c6_6, c6_7, c6_8, c6_9, c6_10]

theorem c7_0 : cK 7 0 = true := by quickRfl
theorem c7_1 : cK 7 1 = true := by quickRfl
theorem c7_2 : cK 7 2 = true := by quickRfl
theorem c7_3 : cK 7 3 = true := by quickRfl
theorem c7_4 : cK 7 4 = true := by quickRfl
theorem c7_5 : cK 7 5 = true := by quickRfl
theorem c7_6 : cK 7 6 = true := by quickRfl
theorem c7_7 : cK 7 7 = true := by quickRfl
theorem c7_8 : cK 7 8 = true := by quickRfl
theorem c7_9 : cK 7 9 = true := by quickRfl
theorem c7_10 : cK 7 10 = true := by quickRfl

theorem s7 : ∀ k₁ < 11, cK 7 k₁ = true := by
  intro k₁ hk
  interval_cases k₁
  exacts [c7_0, c7_1, c7_2, c7_3, c7_4, c7_5, c7_6, c7_7, c7_8, c7_9, c7_10]

end CertificateChecks.KernelLC.M12Over

end
