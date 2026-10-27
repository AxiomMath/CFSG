module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree

public section

namespace CertificateChecks.Gl3064

@[expose] def R2Text : String := include_str "Gl3064/gl2_rec.hex"
@[expose] def E2Text : String := include_str "Gl3064/gl2_edge.hex"
@[expose] def R3Text : String := include_str "Gl3064/gl3_rec.hex"
@[expose] def E3Text : String := include_str "Gl3064/gl3_edge.hex"

@[expose] noncomputable def R2 : Nat → Nat := by hex_tree R2Text 192 9843979155998265464 192
@[expose] noncomputable def E2 : Nat → Nat := by hex_tree E2Text 128 17807196210405784724 128
@[expose] noncomputable def R3 : Nat → Nat := by hex_tree R3Text 1152 16979167726394601151 384
@[expose] noncomputable def E3 : Nat → Nat := by hex_tree E3Text 1920 8930871094145930890 640

end CertificateChecks.Gl3064

end
