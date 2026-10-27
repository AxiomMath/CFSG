module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveFinite

public section

namespace CertificateChecks.KernelHSStd

open CFSG.EvenSporadicStandard.HSStd

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
theorem s5ThreeGuarded :
    ∀ τ : Equiv.Perm (Fin 5), τ * τ = 1 → τ ≠ 1 →
      ∀ μ₁ : Equiv.Perm (Fin 5), μ₁ * μ₁ = 1 → τ * μ₁ = μ₁ * τ →
        ∀ μ₂ : Equiv.Perm (Fin 5), μ₂ * μ₂ = 1 → τ * μ₂ = μ₂ * τ →
          (μ₁ * μ₂) ^ 3 = 1 → μ₁ * μ₂ ≠ 1 →
            ∃ i j k l : Fin 5, i ≠ j ∧ k ≠ l ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧
              τ = Equiv.swap i j ∧ (μ₁ = Equiv.swap k l ∨ μ₁ * τ = Equiv.swap k l) := by
  decide +kernel

theorem s5ThreeProp_kernel : S5ThreeProp :=
  fun τ μ₁ μ₂ hτ hτ1 hμ₁ hμ₂ h3 h1 hc₁ hc₂ => s5ThreeGuarded τ hτ hτ1 μ₁ hμ₁ hc₁ μ₂ hμ₂ hc₂ h3 h1

end CertificateChecks.KernelHSStd
