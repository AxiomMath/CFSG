module

public import Certificates.Data.Kernel.MonsterB.QForm
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.HexNat

public section

namespace CertificateChecks.Orb3132

open CFSG.KLie.CT CFSG.KC.QForm

@[expose] def TText : String := include_str "Orb3132/tabs.hex"
@[expose] def MText : String := include_str "Orb3132/mats.hex"
@[expose] def PText : String := include_str "Orb3132/omp.hex"

@[expose] noncomputable def TT : Nat → Nat := by
  hex_tree TText 71808 10164463665879594255 1408
@[expose] noncomputable def MM : Nat := by hex_nat MText 2055 13281060144937699995
@[expose] noncomputable def PP : Nat → Nat := by hex_tree PText 234600 8679831320721450120 6900

@[expose] noncomputable def U : Nat :=
  441711976819182558062562059991242108775384189333654148116072953081362912

@[expose] noncomputable def mat (k : Nat) : Nat := fget MM k (nat_lit 484)

@[expose] noncomputable def act (k v : Nat) : Nat := actB TT k v

end CertificateChecks.Orb3132

end
