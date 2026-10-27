module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree

public section

namespace CertificateChecks.Diag3031

@[expose] def RText : String := include_str "Diag3031/d_rec.hex"
@[expose] def EText : String := include_str "Diag3031/d_edge.hex"

@[expose] noncomputable def R : Nat → Nat := by hex_tree RText 420480 8420285774386681370 4672
@[expose] noncomputable def E : Nat → Nat := by hex_tree EText 57600 6836088200369901045 640

end CertificateChecks.Diag3031

end
