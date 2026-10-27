module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree

public section

namespace CertificateChecks.Orb3132

@[expose] def R39Text : String := include_str "Orb3132/o39_rec.hex"

@[expose] noncomputable def R39 : Nat → Nat := by hex_tree R39Text 2965248 257714334005425807 832

end CertificateChecks.Orb3132

end
