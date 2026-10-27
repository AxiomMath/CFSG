module

public import Certificates.Kernel.LocalComp.M12Over.S0
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Over

theorem c4_0 : cK 4 0 = true := by quickRfl
theorem c4_1 : cK 4 1 = true := by quickRfl
theorem c4_2 : cK 4 2 = true := by quickRfl
theorem c4_3 : cK 4 3 = true := by quickRfl
theorem c4_4 : cK 4 4 = true := by quickRfl
theorem c4_5 : cK 4 5 = true := by quickRfl
theorem c4_6 : cK 4 6 = true := by quickRfl
theorem c4_7 : cK 4 7 = true := by quickRfl
theorem c4_8 : cK 4 8 = true := by quickRfl
theorem c4_9 : cK 4 9 = true := by quickRfl
theorem c4_10 : cK 4 10 = true := by quickRfl

theorem s4 : ∀ k₁ < 11, cK 4 k₁ = true := by
  intro k₁ hk
  interval_cases k₁
  exacts [c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10]

theorem c5_0 : cK 5 0 = true := by quickRfl
theorem c5_1 : cK 5 1 = true := by quickRfl
theorem c5_2 : cK 5 2 = true := by quickRfl
theorem c5_3 : cK 5 3 = true := by quickRfl
theorem c5_4 : cK 5 4 = true := by quickRfl
theorem c5_5 : cK 5 5 = true := by quickRfl
theorem c5_6 : cK 5 6 = true := by quickRfl
theorem c5_7 : cK 5 7 = true := by quickRfl
theorem c5_8 : cK 5 8 = true := by quickRfl
theorem c5_9 : cK 5 9 = true := by quickRfl
theorem c5_10 : cK 5 10 = true := by quickRfl

theorem s5 : ∀ k₁ < 11, cK 5 k₁ = true := by
  intro k₁ hk
  interval_cases k₁
  exacts [c5_0, c5_1, c5_2, c5_3, c5_4, c5_5, c5_6, c5_7, c5_8, c5_9, c5_10]

end CertificateChecks.KernelLC.M12Over

end
