module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree

public section

namespace CertificateChecks.Orb3132

@[expose] def R35cText : String := include_str "Orb3132/o35_rec2.hex"

@[expose] noncomputable def R35c : Nat → Nat := by
  hex_tree R35cText 3459456 12330774187818234839 832

end CertificateChecks.Orb3132

end
