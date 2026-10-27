module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree

public section

namespace CertificateChecks.Conj3052

@[expose] def A2Text : String := include_str "Conj3052/a2_rec.hex"
@[expose] def A2EText : String := include_str "Conj3052/a2_edge.hex"
@[expose] def A3Text : String := include_str "Conj3052/a3_rec.hex"
@[expose] def A3EText : String := include_str "Conj3052/a3_edge.hex"

@[expose] noncomputable def A2 : Nat → Nat := by hex_tree A2Text 38912 906689839686754036 2048
@[expose] noncomputable def A2E : Nat → Nat := by
  hex_tree A2EText 10944 15685464857161712759 576
@[expose] noncomputable def A3 : Nat → Nat := by hex_tree A3Text 12288 4414361029612858570 2048
@[expose] noncomputable def A3E : Nat → Nat := by
  hex_tree A3EText 2688 10055454507181913423 448

end CertificateChecks.Conj3052

end
