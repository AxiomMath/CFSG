
module

public import Certificates.Kernel.GammaUStepA.Checks
public import CFSG.Certificates.Kernel.GammaUStepA.Sound

public section

namespace CFSG.KD.GUA

open CFSG.KC.GUA CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem t1_16964 : ∀ rep ∈ dReps, rep ≠ d0 →
    ∀ L : Subgroup (V12 ≃ₗ[ZMod 2] V12), ¬ Hyp (vecOf a0) (spanOf rep) L :=
  t1_spec cs16964_theta cs16964_t1r0 cs16964_t1r2 cs16964_bad3 cs16964_t1r4 cs16964_t1r5

theorem t2_16964 : ∀ L : Subgroup (V12 ≃ₗ[ZMod 2] V12), Hyp (vecOf a0) (spanOf d0) L →
    ∃ c < 32, ∀ l : V12 ≃ₗ[ZMod 2] V12, l ∈ L ↔ ∃ r ∈ compOf c, ∀ x, l x = linOfRows r x :=
  t2_spec cs16964_pin cs16964_theta cs16964_b10 cs16964_coef cs16964_span cs16964_perp
    cs16964_ker cs16964_gens cs16964_comm cs16964_rho

theorem t3_16964 : ∀ c < 32, ∀ r ∈ compOf c, r.size = 12 ∧ ∀ x ∈ r, x < 4096 :=
  t3_spec cs16964_pin

end CFSG.KD.GUA

end
