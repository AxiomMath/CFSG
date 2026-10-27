
module

public import Certificates.Kernel.GammaUStepA.Checks
public import Certificates.Kernel.GammaUStepA.ClassChecks
public import CFSG.Certificates.Kernel.GammaUStepA.ClassSound

public section

namespace CFSG.KD.GUA

open CFSG.KC.GUA CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem class_16965 : ∀ c < 32, ∃ i, (i = 0 ∨ i = 1) ∧ ∃ g ∈ gammaU, g (vecOf a0) = vecOf a0 ∧
    (∀ y, y ∈ spanOf d0 ↔ g y ∈ spanOf d0) ∧
    ∀ l : V12 ≃ₗ[ZMod 2] V12, (∃ r ∈ compOf c, ∀ x, l x = linOfRows r x) ↔
      ∃ r ∈ compOf i, ∀ x, (g⁻¹ * l * g) x = linOfRows r x :=
  cls_spec cs16964_pin cs16964_span cs16964_comm cs16965_b0 cs16965_b1 cs16965_b2 cs16965_b3

end CFSG.KD.GUA

end
