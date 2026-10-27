module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree

public section

namespace CertificateChecks.Sp8Orb

@[expose] def VRText : String := include_str "Sp8Orb/vec_rec.hex"
@[expose] def VEText : String := include_str "Sp8Orb/vec_edge.hex"
@[expose] def TRText : String := include_str "Sp8Orb/tup_rec.hex"
@[expose] def TEText : String := include_str "Sp8Orb/tup_edge.hex"

@[expose] noncomputable def VR : Nat → Nat := by hex_tree VRText 1792 14326375400116905582 448
@[expose] noncomputable def VE : Nat → Nat := by hex_tree VEText 23040 7326271279169749439 5760
@[expose] noncomputable def TR : Nat → Nat := by hex_tree TRText 6144 4379979266662078755 3072
@[expose] noncomputable def TE : Nat → Nat := by hex_tree TEText 5248 7425208743065024045 2624

end CertificateChecks.Sp8Orb

end
