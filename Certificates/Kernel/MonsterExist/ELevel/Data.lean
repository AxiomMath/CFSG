module

public import CFSG.Certificates.Kernel.Common.HexNat

public section

namespace CertificateChecks.MonsterExist.ELevel

@[expose] def CV1Text : String := include_str "el1_cv.hex"

@[expose] def CS1Text : String := include_str "el1_cs.hex"

@[expose] def CV2Text : String := include_str "el2_cv.hex"

@[expose] def CS2Text : String := include_str "el2_cs.hex"

@[expose] def TT1Text : String := include_str "el1_tt.hex"

@[expose] def TT2Text : String := include_str "el2_tt.hex"

@[expose] def TT6Text : String := include_str "el6_tt.hex"

@[expose] noncomputable def TT1 : Nat := by
  hex_nat TT1Text 7678 6990758202264536701

@[expose] noncomputable def TT2 : Nat := by
  hex_nat TT2Text 7676 4470876416036731940

@[expose] noncomputable def TT6 : Nat := by
  hex_nat TT6Text 7678 14310987588355250181

@[expose] noncomputable def CV1 : Nat := by
  hex_nat CV1Text 14250 17240582936430795352

@[expose] noncomputable def CS1 : Nat := by
  hex_nat CS1Text 750 13215864303618960145

@[expose] noncomputable def CV2 : Nat := by
  hex_nat CV2Text 1650 14246705285241451766

@[expose] noncomputable def CS2 : Nat := by
  hex_nat CS2Text 1650 14246705285241451766

end CertificateChecks.MonsterExist.ELevel

end
