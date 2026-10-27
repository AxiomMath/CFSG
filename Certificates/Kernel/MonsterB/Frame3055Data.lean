module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.HexNat

public section

namespace CertificateChecks.Frame3055

@[expose] def PText : String := include_str "Frame3055/frame_perm.hex"
@[expose] def OText : String := include_str "Frame3055/oct_keys.hex"
@[expose] def FText : String := include_str "Frame3055/f_rec.hex"
@[expose] def FEText : String := include_str "Frame3055/f_edge.hex"

@[expose] def GText : String := include_str "Frame3055/f_gens.hex"

@[expose] noncomputable def GF : Nat := by hex_nat GText 270 7373532244879186826
@[expose] noncomputable def PD : Nat := by hex_nat PText 1985 17148408426030172505
@[expose] noncomputable def OK : Nat := by hex_nat OText 444 8779845920086553450
@[expose] noncomputable def F : Nat → Nat := by hex_tree FText 391680 7443553236410209848 2176
@[expose] noncomputable def FE : Nat → Nat := by hex_tree FEText 368640 11136617807607385179 2048

end CertificateChecks.Frame3055

end
