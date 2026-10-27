module

public import Certificates.Data.Kernel.O8.ModelW
public import Certificates.Kernel.OmegaEight.CPChains
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.O8

theorem kS5ElemM : ∀ b < 16, s5ElemOK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩ b = true := by
  intro b hb
  interval_cases b <;> quickRfl

end CertificateChecks.KernelO8

end
