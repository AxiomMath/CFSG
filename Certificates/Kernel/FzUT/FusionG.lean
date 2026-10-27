module

public import Certificates.Kernel.FzUT.Triple
public import Certificates.Kernel.FzUT.Rep3
public import CFSG.Certificates.Kernel.FzUT.FusionT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10SpecD

public section

namespace CFSG.KC.FzUT

open CFSG.OddStandard.SmallF3.FritzII

theorem fusion_of_reps (hR : ∀ t s l, FzValidTriple t s l → ∀ k < 3,
    gc t = 14765201 → gc s = fldN (fldN N3.RP 48 281474976710655 k) 24 16777215 0 →
    gc l = fldN (fldN N3.RP 48 281474976710655 k) 24 16777215 1 →
    ¬ ∃ θ : ℕ → Prop, FzRules (parT t s l) θ) : FzFusionSpec := by
  intro t s l h
  refine N3.norm_reps (fun t s l => (∀ x₁, FzValidX t l x₁ → FzShape t s l x₁) ∨
      ¬ ∃ θ : ℕ → Prop, FzRules (parT t s l) θ) ?_ ?_ ?_ t s l h
  · intro β t s l hβ h'
    rcases h' with h' | h'
    · exact Or.inl fun x₁ hx => shape_cj β (h' (β x₁) (validX_cj β hx))
    · exact Or.inr (fusion_cj β hβ h')
  · intro t s l _ hv
    exact Or.inl fun x₁ hx => absurd hx (hv x₁)
  · intro t s l hv k hk ht hs hl
    rw [Sh.t0_code] at ht
    by_cases h3 : k = 3
    · subst h3
      rw [Sh.rep3_codes.1] at hs
      rw [Sh.rep3_codes.2] at hl
      exact Or.inl fun x₁ hx => Sh.rep3_shape t s l ht hs hl x₁ hx
    · exact Or.inr (hR t s l hv k (by omega) ht hs hl)

end CFSG.KC.FzUT
