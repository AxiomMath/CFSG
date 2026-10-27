module

public import CFSG.Certificates.Kernel.E6RegInnerSound
public import Certificates.Kernel.E6RegPair.Assembly
public import Certificates.Kernel.E6RegPair.InnerChecks

public section

namespace CertificateChecks.KernelE6RegPair

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.KC.E6RegInner CFSG.KD.E6RegPair

theorem e6RegularInnerLine :
    ∀ (b₁ b₂ : Fin Tag.E6.rank → ZMod 3),
      (∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ¬ (triPairing b₁ α = 0 ∧ triPairing b₂ α = 0)) →
      ∀ w : WeylGroup Tag.E6, w ∈ charStabilizer (triChar b₁) → w ∈ charStabilizer (triChar b₂) →
        (triPairing b₁ (e6Shift w) ≠ 0 ∨ triPairing b₂ (e6Shift w) ≠ 0) →
        ∀ c₁ c₂ : ZMod 3, (c₁ ≠ 0 ∨ c₂ ≠ 0) →
          triPairing (c₁ • b₁ + c₂ • b₂) (e6Shift w) = 0 →
          ∃ β₁ β₂ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β₁ ∧ IsRoot Tag.E6 β₂ ∧
            IsRoot Tag.E6 (β₁ + β₂) ∧ triPairing (c₁ • b₁ + c₂ • b₂) β₁ = 0 ∧
            triPairing (c₁ • b₁ + c₂ • b₂) β₂ = 0 ∧ w • β₁ = β₁ ∧ w • β₂ = β₂ :=
  e6RegularInnerLine_of_checks rows_check partners_check stab_check orbit7_check inner_check

end CertificateChecks.KernelE6RegPair
