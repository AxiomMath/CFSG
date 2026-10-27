module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.HexNat

public section

namespace CertificateChecks.Six3056

@[expose] def MText : String := include_str "Six3056/mats.hex"
@[expose] def TText : String := include_str "Six3056/tabs.hex"
@[expose] def SText : String := include_str "Six3056/s_rec.hex"
@[expose] def SEText : String := include_str "Six3056/s_edge.hex"

@[expose] noncomputable def MM : Nat := by hex_nat MText 2420 4838792439859920358
@[expose] noncomputable def TT : Nat → Nat := by hex_tree TText 84480 1103579241056226816 1408
@[expose] noncomputable def S : Nat → Nat := by hex_tree SText 898560 8601070530191460462 2496
@[expose] noncomputable def SE : Nat → Nat := by hex_tree SEText 1728000 721204791772624530 4800

end CertificateChecks.Six3056

end
