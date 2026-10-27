module

public import Certificates.Kernel.LocalComp.M12Over.S2
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Over

theorem c8_0 : cK 8 0 = true := by quickRfl
theorem c8_1 : cK 8 1 = true := by quickRfl
theorem c8_2 : cK 8 2 = true := by quickRfl
theorem c8_3 : cK 8 3 = true := by quickRfl
theorem c8_4 : cK 8 4 = true := by quickRfl
theorem c8_5 : cK 8 5 = true := by quickRfl
theorem c8_6 : cK 8 6 = true := by quickRfl
theorem c8_7 : cK 8 7 = true := by quickRfl
theorem c8_8 : cK 8 8 = true := by quickRfl
theorem c8_9 : cK 8 9 = true := by quickRfl
theorem c8_10 : cK 8 10 = true := by quickRfl

theorem s8 : ∀ k₁ < 11, cK 8 k₁ = true := by
  intro k₁ hk
  interval_cases k₁
  exacts [c8_0, c8_1, c8_2, c8_3, c8_4, c8_5, c8_6, c8_7, c8_8, c8_9, c8_10]

theorem c9_0 : cK 9 0 = true := by quickRfl
theorem c9_1 : cK 9 1 = true := by quickRfl
theorem c9_2 : cK 9 2 = true := by quickRfl
theorem c9_3 : cK 9 3 = true := by quickRfl
theorem c9_4 : cK 9 4 = true := by quickRfl
theorem c9_5 : cK 9 5 = true := by quickRfl
theorem c9_6 : cK 9 6 = true := by quickRfl
theorem c9_7 : cK 9 7 = true := by quickRfl
theorem c9_8 : cK 9 8 = true := by quickRfl
theorem c9_9 : cK 9 9 = true := by quickRfl
theorem c9_10 : cK 9 10 = true := by quickRfl

theorem s9 : ∀ k₁ < 11, cK 9 k₁ = true := by
  intro k₁ hk
  interval_cases k₁
  exacts [c9_0, c9_1, c9_2, c9_3, c9_4, c9_5, c9_6, c9_7, c9_8, c9_9, c9_10]

end CertificateChecks.KernelLC.M12Over

end
