module

public import Certificates.Kernel.HN1408.CayleyCodes
public import Certificates.Kernel.HN1408.Tab6CayDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.KD.HN1408

open CFSG.EvenSporadicStandard.HNRecog.Section3

@[expose] def d8Enc : DihedralGroup 4 → Nat
  | .r i => i.val
  | .sr i => 4 + i.val

@[expose] def d8Code : CodeM (DihedralGroup 4) where
  enc := d8Enc
  mulC := d8Mul
  inj := by
    intro x y
    revert x y
    decide +kernel
  hom := by decide +kernel

theorem d8Enc_lt (x : DihedralGroup 4) : d8Enc x < 8 := by
  revert x
  decide +kernel

@[expose] def s3Enc (σ : Equiv.Perm (Fin 3)) : Nat := (σ 0).val + 3 * (σ 1).val

@[expose] def s3Code : CodeM (Equiv.Perm (Fin 3)) where
  enc := s3Enc
  mulC := s3Mul
  inj := by
    intro x y
    revert x y
    decide +kernel
  hom := by decide +kernel

@[expose] def e2Enc (v : Multiplicative (Fin 2 → ZMod 2)) : Nat :=
  (Multiplicative.toAdd v 0).val + 2 * (Multiplicative.toAdd v 1).val

@[expose] def e2Code : CodeM (Multiplicative (Fin 2 → ZMod 2)) where
  enc := e2Enc
  mulC := e2Mul
  inj := by
    intro x y
    revert x y
    decide +kernel
  hom := by decide +kernel

theorem e2Enc_lt (v : Multiplicative (Fin 2 → ZMod 2)) : e2Enc v < 4 := by
  revert v
  decide +kernel

@[expose] def t6Code2 : CodeM (DihedralGroup 4 × Sym 3) := prodCode d8Code s3Code 8 d8Enc_lt

@[expose] def t6Code4 : CodeM (Multiplicative (Fin 2 → ZMod 2) × DihedralGroup 4) :=
  prodCode e2Code d8Code 4 e2Enc_lt

@[expose] def t6Code6 : CodeM (Z 2 × DihedralGroup 5) := prodCode (zCode 2) d10Code 2 (zEnc_lt 2)

@[expose] def t6Code7 : CodeM (Z 2 × DihedralGroup 4) := prodCode (zCode 2) d8Code 2 (zEnc_lt 2)

end CFSG.KD.HN1408

end
