module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree

public section

namespace CertificateChecks.Orb3132

@[expose] def R35aText : String := include_str "Orb3132/o35_rec0.hex"

@[expose] noncomputable def R35a : Nat → Nat := by hex_tree R35aText 3459456 4361517187650389728 832

end CertificateChecks.Orb3132

end
