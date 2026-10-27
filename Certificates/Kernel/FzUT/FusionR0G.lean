module

public import Certificates.Kernel.FzUT.FusionG
public import Certificates.Kernel.FzUT.FusionR0
public import CFSG.Certificates.Kernel.FzUT.Fusion

public section

namespace CFSG.KC.FzUT

open CFSG.OddStandard.SmallF3.FritzII

theorem rp0_codes : fldN (fldN N3.RP 48 281474976710655 0) 24 16777215 0 = 14762113 ∧
    fldN (fldN N3.RP 48 281474976710655 0) 24 16777215 1 = 1081410 := by
  decide +kernel

theorem fusion_r0 (t s l : MulAut FzUT) (ht : gc t = 14765201)
    (hs : gc s = fldN (fldN N3.RP 48 281474976710655 0) 24 16777215 0)
    (hl : gc l = fldN (fldN N3.RP 48 281474976710655 0) 24 16777215 1) :
    ¬ ∃ θ : ℕ → Prop, FzRules (parT t s l) θ := by
  rw [rp0_codes.1] at hs
  rw [rp0_codes.2] at hl
  have hP := fuPar_parT t s l
  rw [ht, hs, hl] at hP
  exact fusion_refute hP R0.ch441790_r0_forest R0.ch441790_r0_dead R0.ch441790_r0_cover

theorem fusion_of_r12 (h1 : ∀ t s l, FzValidTriple t s l → gc t = 14765201 →
      gc s = fldN (fldN N3.RP 48 281474976710655 1) 24 16777215 0 →
      gc l = fldN (fldN N3.RP 48 281474976710655 1) 24 16777215 1 →
      ¬ ∃ θ : ℕ → Prop, FzRules (parT t s l) θ)
    (h2 : ∀ t s l, FzValidTriple t s l → gc t = 14765201 →
      gc s = fldN (fldN N3.RP 48 281474976710655 2) 24 16777215 0 →
      gc l = fldN (fldN N3.RP 48 281474976710655 2) 24 16777215 1 →
      ¬ ∃ θ : ℕ → Prop, FzRules (parT t s l) θ) : FzFusionSpec := by
  refine fusion_of_reps fun t s l hv k hk ht hs hl => ?_
  interval_cases k
  · exact fusion_r0 t s l ht hs hl
  · exact h1 t s l hv ht hs hl
  · exact h2 t s l hv ht hs hl

end CFSG.KC.FzUT
