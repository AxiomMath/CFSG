module

public import Certificates.Kernel.FzUT.Norm3
public import CFSG.Certificates.Kernel.FzUT.Norm3

public section

namespace CFSG.KC.FzUT.N3

open CFSG.OddStandard.SmallF3.FritzII

theorem tg3 : fldN TG 24 16777215 3 = 0 := by decide +kernel

theorem norm_reps (P : MulAut FzUT → MulAut FzUT → MulAut FzUT → Prop)
    (hP : ∀ β t s l, (∀ x, β (fzRho0 x) = fzRho0 (β x)) → P (cj β t) (cj β s) (cj β l) →
      P t s l)
    (hvac : ∀ t s l, FzValidTriple t s l → (∀ x₁, ¬ FzValidX t l x₁) → P t s l)
    (hrep : ∀ t s l, FzValidTriple t s l → ∀ k < 4, gc t = fldN TG 24 16777215 0 →
      gc s = fldN (fldN RP 48 281474976710655 k) 24 16777215 0 →
      gc l = fldN (fldN RP 48 281474976710655 k) 24 16777215 1 → P t s l) :
    ∀ t s l, FzValidTriple t s l → P t s l :=
  norm_sound ch441782_t ch441782_t1 ch441782_t2 tg3 ch441782_iv ch441782_fix ch441782_l
    ch441782_s P hP hvac hrep

theorem classA_of_reps (hrep : ∀ t s l, FzValidTriple t s l → ∀ k < 4,
    gc t = fldN TG 24 16777215 0 → gc s = fldN (fldN RP 48 281474976710655 k) 24 16777215 0 →
    gc l = fldN (fldN RP 48 281474976710655 k) 24 16777215 1 →
    (∀ x₁, FzValidX t l x₁ → FzShape t s l x₁) ∨ FzAutW t s l) : FzClassSpecA :=
  classA_of_norm ch441782_t ch441782_t1 ch441782_t2 tg3 ch441782_iv ch441782_fix ch441782_l
    ch441782_s hrep

end CFSG.KC.FzUT.N3
