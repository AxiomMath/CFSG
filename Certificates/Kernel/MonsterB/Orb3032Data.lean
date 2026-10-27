module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree

public section

namespace CertificateChecks.Orb3032

@[expose] def RText : String := include_str "Orb3032/orb_rec.hex"
@[expose] def EText : String := include_str "Orb3032/orb_edge.hex"

@[expose] noncomputable def R : Nat → Nat := by hex_tree RText 256 9718970686568077251 256
@[expose] noncomputable def E : Nat → Nat := by hex_tree EText 192 17962575095705042041 192

end CertificateChecks.Orb3032

end
