module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.HexNat

public section

namespace CertificateChecks.Mono3016

@[expose] def MText : String := include_str "Mono3016/m_rec.hex"
@[expose] def METext : String := include_str "Mono3016/m_edge.hex"
@[expose] def WText : String := include_str "Mono3016/m_wit.hex"
@[expose] def XText : String := include_str "Mono3016/xj.hex"
@[expose] def PText : String := include_str "Mono3016/pj.hex"

@[expose] noncomputable def M : Nat → Nat := by hex_tree MText 26880 2660643850584165011 768
@[expose] noncomputable def ME : Nat → Nat := by hex_tree METext 105280 1825783119174635141 3008
@[expose] noncomputable def WT : Nat → Nat := by hex_tree WText 6720 10813010845572109690 192
@[expose] noncomputable def XJ : Nat := by hex_nat XText 210 5138616255062195112
@[expose] noncomputable def PJ : Nat := by hex_nat PText 450 8868045389795632856

@[expose] noncomputable def DD : Nat :=
  23210294991508512262946635057163850652213029259520673834274227660135801556368883726

end CertificateChecks.Mono3016

end
