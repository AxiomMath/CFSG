module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree

public section

namespace CertificateChecks.Orb3132

@[expose] def R35bText : String := include_str "Orb3132/o35_rec1.hex"

@[expose] noncomputable def R35b : Nat → Nat := by
  hex_tree R35bText 3459456 12727874203822615323 832

end CertificateChecks.Orb3132

end
