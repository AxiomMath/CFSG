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

theorem kS5AdjP : ∀ b < 6,
    s5AdjNegOK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩ MdCLSP MdREPSP MdNCP MdADJP b = true := by
  intro b hb
  interval_cases b <;> quickRfl

theorem kS5AdjM : ∀ b < 6,
    s5AdjNegOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ MdCLSM MdREPSM MdNCM MdADJM b = true := by
  intro b hb
  interval_cases b <;> quickRfl

end CertificateChecks.KernelO8

end
