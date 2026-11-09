module

public import Certificates.Data.Kernel.O8.ModelW
public import Certificates.Kernel.OmegaEight.CPChains
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.O8

theorem kS5ElemP_0 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 0 = true := by quickRfl
theorem kS5ElemP_1 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 1 = true := by quickRfl
theorem kS5ElemP_2 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 2 = true := by quickRfl
theorem kS5ElemP_3 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 3 = true := by quickRfl
theorem kS5ElemP_4 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 4 = true := by quickRfl
theorem kS5ElemP_5 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 5 = true := by quickRfl
theorem kS5ElemP_6 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 6 = true := by quickRfl
theorem kS5ElemP_7 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 7 = true := by quickRfl
theorem kS5ElemP_8 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 8 = true := by quickRfl
theorem kS5ElemP_9 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 9 = true := by quickRfl
theorem kS5ElemP_10 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 10 = true := by quickRfl
theorem kS5ElemP_11 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 11 = true := by quickRfl
theorem kS5ElemP_12 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 12 = true := by quickRfl
theorem kS5ElemP_13 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 13 = true := by quickRfl
theorem kS5ElemP_14 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 14 = true := by quickRfl
theorem kS5ElemP_15 : s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ 15 = true := by quickRfl

theorem kS5ElemP : ∀ b < 16, s5ElemOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ b = true := by
  intro b hb
  interval_cases b
  exacts [kS5ElemP_0, kS5ElemP_1, kS5ElemP_2, kS5ElemP_3, kS5ElemP_4, kS5ElemP_5, kS5ElemP_6, kS5ElemP_7,
    kS5ElemP_8, kS5ElemP_9, kS5ElemP_10, kS5ElemP_11, kS5ElemP_12, kS5ElemP_13, kS5ElemP_14, kS5ElemP_15]

end CertificateChecks.KernelO8

end
