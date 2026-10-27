module

public import Certificates.Kernel.FzUT.Shape
public import Certificates.Kernel.FzUT.Norm3
public import CFSG.Certificates.Kernel.FzUT.Shape

public section

namespace CFSG.KC.FzUT.Sh

open CFSG.OddStandard.SmallF3.FritzII

theorem t0_code : fldN N3.TG 24 16777215 0 = 14765201 := by decide +kernel

theorem rep3_codes : fldN (fldN N3.RP 48 281474976710655 3) 24 16777215 0 = 10699937 ∧
    fldN (fldN N3.RP 48 281474976710655 3) 24 16777215 1 = 270600 := by
  decide +kernel

theorem rep3_shape (t s l : MulAut FzUT) (ht : gc t = 14765201) (hs : gc s = 10699937)
    (hl : gc l = 270600) (x₁ : FzUT) (hx : FzValidX t l x₁) : FzShape t s l x₁ :=
  shape_sound (SR := SR) (by rw [ht, hs, hl]; exact ch441782_shape) x₁ hx

end CFSG.KC.FzUT.Sh
