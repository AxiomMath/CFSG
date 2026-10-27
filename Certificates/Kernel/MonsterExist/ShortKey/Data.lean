module

public import CFSG.Certificates.Kernel.Common.HexNat

public section

namespace CertificateChecks.MonsterExist.ShortKey

@[expose] def VText : String := include_str "shortkey_v.hex"

@[expose] def PText : String := include_str "shortkey_p.hex"

@[expose] def OText : String := include_str "shortkey_o.hex"

@[expose] noncomputable def SKV : Nat := by
  hex_nat VText 319410 1056371912362686189

@[expose] noncomputable def SKP : Nat := by
  hex_nat PText 786233 14186560721875614482

@[expose] noncomputable def SKO : Nat := by
  hex_nat OText 26624 12527981837589161543

end CertificateChecks.MonsterExist.ShortKey

end
