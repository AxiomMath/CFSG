module

public import Certificates.Data.Kernel.O8.ModelW
public import Certificates.Kernel.OmegaEight.CPChains
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.O8

theorem kS5ElemM_0 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 0 = true := by quickRfl
theorem kS5ElemM_1 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 1 = true := by quickRfl
theorem kS5ElemM_2 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 2 = true := by quickRfl
theorem kS5ElemM_3 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 3 = true := by quickRfl
theorem kS5ElemM_4 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 4 = true := by quickRfl
theorem kS5ElemM_5 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 5 = true := by quickRfl
theorem kS5ElemM_6 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 6 = true := by quickRfl
theorem kS5ElemM_7 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 7 = true := by quickRfl
theorem kS5ElemM_8 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 8 = true := by quickRfl
theorem kS5ElemM_9 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 9 = true := by quickRfl
theorem kS5ElemM_10 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 10 = true := by quickRfl
theorem kS5ElemM_11 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 11 = true := by quickRfl
theorem kS5ElemM_12 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 12 = true := by quickRfl
theorem kS5ElemM_13 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 13 = true := by quickRfl
theorem kS5ElemM_14 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 14 = true := by quickRfl
theorem kS5ElemM_15 : s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ 15 = true := by quickRfl

theorem kS5ElemM : ∀ b < 16, s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ b = true := by
  intro b hb
  interval_cases b
  exacts [kS5ElemM_0, kS5ElemM_1, kS5ElemM_2, kS5ElemM_3, kS5ElemM_4, kS5ElemM_5, kS5ElemM_6, kS5ElemM_7,
    kS5ElemM_8, kS5ElemM_9, kS5ElemM_10, kS5ElemM_11, kS5ElemM_12, kS5ElemM_13, kS5ElemM_14, kS5ElemM_15]

end CertificateChecks.KernelO8

end
