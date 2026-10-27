module

public import Certificates.Kernel.FzUT.Triple
public import Certificates.Kernel.FzUT.Rep3

public section

namespace CFSG.KC.FzUT

open CFSG.OddStandard.SmallF3.FritzII

theorem classA_of_autW (h : ∀ k < 3, ∀ t s l, FzValidTriple t s l → gc t = 14765201 →
    gc s = fldN (fldN N3.RP 48 281474976710655 k) 24 16777215 0 →
    gc l = fldN (fldN N3.RP 48 281474976710655 k) 24 16777215 1 → FzAutW t s l) :
    FzClassSpecA := by
  refine N3.classA_of_reps fun t s l hv k hk ht hs hl => ?_
  rw [Sh.t0_code] at ht
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · exact Or.inr (h k hk3 t s l hv ht hs hl)
  · obtain rfl : k = 3 := by omega
    rw [Sh.rep3_codes.1] at hs
    rw [Sh.rep3_codes.2] at hl
    exact Or.inl (Sh.rep3_shape t s l ht hs hl)

end CFSG.KC.FzUT
