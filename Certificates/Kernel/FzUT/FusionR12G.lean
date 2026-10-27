module

public import Certificates.Kernel.FzUT.FusionR1
public import Certificates.Kernel.FzUT.FusionR2
public import CFSG.Certificates.Kernel.FzUT.FusionP
public import Certificates.Kernel.FzUT.Norm3

public section

namespace CFSG.KC.FzUT

open CFSG.OddStandard.SmallF3.FritzII CFSG.KD

theorem rp12_codes : fldN (fldN N3.RP 48 281474976710655 1) 24 16777215 0 = 528900 ∧
    fldN (fldN N3.RP 48 281474976710655 1) 24 16777215 1 = 1081410 ∧
    fldN (fldN N3.RP 48 281474976710655 2) 24 16777215 0 = 528900 ∧
    fldN (fldN N3.RP 48 281474976710655 2) 24 16777215 1 = 270600 := by
  decide +kernel

theorem fusion_r1 (t s l : MulAut FzUT) (_ : FzValidTriple t s l) (ht : gc t = 14765201)
    (hs : gc s = fldN (fldN N3.RP 48 281474976710655 1) 24 16777215 0)
    (hl : gc l = fldN (fldN N3.RP 48 281474976710655 1) 24 16777215 1) :
    ¬ ∃ θ : ℕ → Prop, FzRules (parT t s l) θ := by
  rw [rp12_codes.1] at hs
  rw [rp12_codes.2.1] at hl
  have hP := fuPar_parT t s l
  rw [ht, hs, hl] at hP
  exact refute_leaves hP R1.ch441790_r1_forest R1.ch441790_r1_dead R1.ch441790_r1_iw
    R1.ch441790_r1_xt R1.ch441790_r1_ts R1.ch441790_r1_tk
    (leaves_of R1.ch441790_r1_leaves0 R1.ch441790_r1_leaves4 R1.ch441790_r1_leaves8
      R1.ch441790_r1_leaves12)

theorem fusion_r2 (t s l : MulAut FzUT) (_ : FzValidTriple t s l) (ht : gc t = 14765201)
    (hs : gc s = fldN (fldN N3.RP 48 281474976710655 2) 24 16777215 0)
    (hl : gc l = fldN (fldN N3.RP 48 281474976710655 2) 24 16777215 1) :
    ¬ ∃ θ : ℕ → Prop, FzRules (parT t s l) θ := by
  rw [rp12_codes.2.2.1] at hs
  rw [rp12_codes.2.2.2] at hl
  have hP := fuPar_parT t s l
  rw [ht, hs, hl] at hP
  exact refute_leaves hP R2.ch441790_r2_forest R2.ch441790_r2_dead R2.ch441790_r2_iw
    R2.ch441790_r2_xt R2.ch441790_r2_ts R2.ch441790_r2_tk
    (leaves_of R2.ch441790_r2_leaves0 R2.ch441790_r2_leaves4 R2.ch441790_r2_leaves8
      R2.ch441790_r2_leaves12)

end CFSG.KC.FzUT
