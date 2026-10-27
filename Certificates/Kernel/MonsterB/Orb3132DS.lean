module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree

public section

namespace CertificateChecks.Orb3132

@[expose] def R60Text : String := include_str "Orb3132/o60_rec.hex"
@[expose] def R32Text : String := include_str "Orb3132/o32_rec.hex"

@[expose] noncomputable def R60 : Nat → Nat := by hex_tree R60Text 15488 11481379921239696464 704
@[expose] noncomputable def R32 : Nat → Nat := by hex_tree R32Text 248832 1730764766848905497 768

end CertificateChecks.Orb3132

end
