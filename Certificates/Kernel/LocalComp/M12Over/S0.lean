module

public import Certificates.Kernel.LocalComp.M12Over.Wit
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Over

theorem c0_0 : cK 0 0 = true := by quickRfl
theorem c0_1 : cK 0 1 = true := by quickRfl
theorem c0_2 : cK 0 2 = true := by quickRfl
theorem c0_3 : cK 0 3 = true := by quickRfl
theorem c0_4 : cK 0 4 = true := by quickRfl
theorem c0_5 : cK 0 5 = true := by quickRfl
theorem c0_6 : cK 0 6 = true := by quickRfl
theorem c0_7 : cK 0 7 = true := by quickRfl
theorem c0_8 : cK 0 8 = true := by quickRfl
theorem c0_9 : cK 0 9 = true := by quickRfl
theorem c0_10 : cK 0 10 = true := by quickRfl

theorem s0 : ∀ k₁ < 11, cK 0 k₁ = true := by
  intro k₁ hk
  interval_cases k₁
  exacts [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10]

theorem c1_0 : cK 1 0 = true := by quickRfl
theorem c1_1 : cK 1 1 = true := by quickRfl
theorem c1_2 : cK 1 2 = true := by quickRfl
theorem c1_3 : cK 1 3 = true := by quickRfl
theorem c1_4 : cK 1 4 = true := by quickRfl
theorem c1_5 : cK 1 5 = true := by quickRfl
theorem c1_6 : cK 1 6 = true := by quickRfl
theorem c1_7 : cK 1 7 = true := by quickRfl
theorem c1_8 : cK 1 8 = true := by quickRfl
theorem c1_9 : cK 1 9 = true := by quickRfl
theorem c1_10 : cK 1 10 = true := by quickRfl

theorem s1 : ∀ k₁ < 11, cK 1 k₁ = true := by
  intro k₁ hk
  interval_cases k₁
  exacts [c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, c1_6, c1_7, c1_8, c1_9, c1_10]

end CertificateChecks.KernelLC.M12Over

end
