module

public import Certificates.Kernel.LocalComp.M12Over.Wit
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Over

theorem c2_0 : cK 2 0 = true := by quickRfl
theorem c2_1 : cK 2 1 = true := by quickRfl
theorem c2_2 : cK 2 2 = true := by quickRfl
theorem c2_3 : cK 2 3 = true := by quickRfl
theorem c2_4 : cK 2 4 = true := by quickRfl
theorem c2_5 : cK 2 5 = true := by quickRfl
theorem c2_6 : cK 2 6 = true := by quickRfl
theorem c2_7 : cK 2 7 = true := by quickRfl
theorem c2_8 : cK 2 8 = true := by quickRfl
theorem c2_9 : cK 2 9 = true := by quickRfl
theorem c2_10 : cK 2 10 = true := by quickRfl

theorem s2 : ∀ k₁ < 11, cK 2 k₁ = true := by
  intro k₁ hk
  interval_cases k₁
  exacts [c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10]

theorem c3_0 : cK 3 0 = true := by quickRfl
theorem c3_1 : cK 3 1 = true := by quickRfl
theorem c3_2 : cK 3 2 = true := by quickRfl
theorem c3_3 : cK 3 3 = true := by quickRfl
theorem c3_4 : cK 3 4 = true := by quickRfl
theorem c3_5 : cK 3 5 = true := by quickRfl
theorem c3_6 : cK 3 6 = true := by quickRfl
theorem c3_7 : cK 3 7 = true := by quickRfl
theorem c3_8 : cK 3 8 = true := by quickRfl
theorem c3_9 : cK 3 9 = true := by quickRfl
theorem c3_10 : cK 3 10 = true := by quickRfl

theorem s3 : ∀ k₁ < 11, cK 3 k₁ = true := by
  intro k₁ hk
  interval_cases k₁
  exacts [c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10]

end CertificateChecks.KernelLC.M12Over

end
