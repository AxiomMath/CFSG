module

public import CFSG.Certificates.Kernel.Common.HexNat

public section

namespace CertificateChecks.MonsterExist.WeylE6

@[expose] def TText : String := include_str "we6t.hex"

@[expose] def PText : String := include_str "we6p.hex"

@[expose] def EText : String := include_str "we6e.hex"

@[expose] noncomputable def WT : Nat := by hex_nat TText 3046 15051036022672809203

@[expose] noncomputable def WP : Nat := by hex_nat PText 622080 11256179567759850692

@[expose] noncomputable def WE : Nat := by hex_nat EText 1451517 12695531339354356176

end CertificateChecks.MonsterExist.WeylE6

end
