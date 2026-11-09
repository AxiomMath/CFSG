module

public import Certificates.Data.Kernel.O8.ModelW
public import Certificates.Kernel.OmegaEight.CPChains
public import Certificates.Kernel.OmegaEight.ModelData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.O8

theorem kS5ClsP_0 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 0 = true := by quickRfl
theorem kS5ClsP_1 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 1 = true := by quickRfl
theorem kS5ClsP_2 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 2 = true := by quickRfl
theorem kS5ClsP_3 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 3 = true := by quickRfl
theorem kS5ClsP_4 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 4 = true := by quickRfl
theorem kS5ClsP_5 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 5 = true := by quickRfl
theorem kS5ClsP_6 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 6 = true := by quickRfl
theorem kS5ClsP_7 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 7 = true := by quickRfl
theorem kS5ClsP_8 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 8 = true := by quickRfl
theorem kS5ClsP_9 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 9 = true := by quickRfl
theorem kS5ClsP_10 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 10 = true := by quickRfl
theorem kS5ClsP_11 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 11 = true := by quickRfl
theorem kS5ClsP_12 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 12 = true := by quickRfl
theorem kS5ClsP_13 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 13 = true := by quickRfl
theorem kS5ClsP_14 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 14 = true := by quickRfl
theorem kS5ClsP_15 : s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP 15 = true := by quickRfl
theorem kS5ClsP : ∀ b < 16,
    s5ClsOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP b = true := by
  intro b hb
  interval_cases b
  exacts [kS5ClsP_0, kS5ClsP_1, kS5ClsP_2, kS5ClsP_3, kS5ClsP_4, kS5ClsP_5, kS5ClsP_6, kS5ClsP_7,
    kS5ClsP_8, kS5ClsP_9, kS5ClsP_10, kS5ClsP_11, kS5ClsP_12, kS5ClsP_13, kS5ClsP_14, kS5ClsP_15]

end CertificateChecks.KernelO8

end
