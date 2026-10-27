module

public import Certificates.Kernel.LocalComp.M12Over.S3
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Over

theorem c10_0 : cK 10 0 = true := by quickRfl
theorem c10_1 : cK 10 1 = true := by quickRfl
theorem c10_2 : cK 10 2 = true := by quickRfl
theorem c10_3 : cK 10 3 = true := by quickRfl
theorem c10_4 : cK 10 4 = true := by quickRfl
theorem c10_5 : cK 10 5 = true := by quickRfl
theorem c10_6 : cK 10 6 = true := by quickRfl
theorem c10_7 : cK 10 7 = true := by quickRfl
theorem c10_8 : cK 10 8 = true := by quickRfl
theorem c10_9 : cK 10 9 = true := by quickRfl
theorem c10_10 : cK 10 10 = true := by quickRfl

theorem s10 : ∀ k₁ < 11, cK 10 k₁ = true := by
  intro k₁ hk
  interval_cases k₁
  exacts [c10_0, c10_1, c10_2, c10_3, c10_4, c10_5, c10_6, c10_7, c10_8, c10_9, c10_10]

theorem c11_0 : cK 11 0 = true := by quickRfl
theorem c11_1 : cK 11 1 = true := by quickRfl
theorem c11_2 : cK 11 2 = true := by quickRfl
theorem c11_3 : cK 11 3 = true := by quickRfl
theorem c11_4 : cK 11 4 = true := by quickRfl
theorem c11_5 : cK 11 5 = true := by quickRfl
theorem c11_6 : cK 11 6 = true := by quickRfl
theorem c11_7 : cK 11 7 = true := by quickRfl
theorem c11_8 : cK 11 8 = true := by quickRfl
theorem c11_9 : cK 11 9 = true := by quickRfl
theorem c11_10 : cK 11 10 = true := by quickRfl

theorem s11 : ∀ k₁ < 11, cK 11 k₁ = true := by
  intro k₁ hk
  interval_cases k₁
  exacts [c11_0, c11_1, c11_2, c11_3, c11_4, c11_5, c11_6, c11_7, c11_8, c11_9, c11_10]

end CertificateChecks.KernelLC.M12Over

end
