module

public import Init
import CFSG.Certificates.Kernel.Common.HexTree
import CFSG.Certificates.Kernel.Common.HexNat

public section

namespace CertificateChecks.Perm3018

@[expose] def SText : String := include_str "Perm3018/s_rec.hex"
@[expose] def SEText : String := include_str "Perm3018/s_edge.hex"
@[expose] def O1Text : String := include_str "Perm3018/o1_rec.hex"
@[expose] def O1EText : String := include_str "Perm3018/o1_edge.hex"
@[expose] def O2Text : String := include_str "Perm3018/o2_rec.hex"
@[expose] def O2EText : String := include_str "Perm3018/o2_edge.hex"
@[expose] def WText : String := include_str "Perm3018/inv_wit.hex"
@[expose] def GText : String := include_str "Perm3018/gens.hex"

@[expose] noncomputable def S : Nat → Nat := by hex_tree SText 35840 12565849704028014618 2240
@[expose] noncomputable def SE : Nat → Nat := by hex_tree SEText 25600 16762767940773724476 1600
@[expose] noncomputable def O1 : Nat → Nat := by hex_tree O1Text 410112 10785561904788136016 2304
@[expose] noncomputable def O1E : Nat → Nat := by hex_tree O1EText 79744 7248868075131085700 448
@[expose] noncomputable def O2 : Nat → Nat := by hex_tree O2Text 1149696 918770891218529069 2304
@[expose] noncomputable def O2E : Nat → Nat := by hex_tree O2EText 255488 10146104304314507192 512
@[expose] noncomputable def W : Nat := by hex_nat WText 4092 6170547446685615448
@[expose] noncomputable def GS : Nat := by hex_nat GText 300 10240353071979726482

@[expose] noncomputable def GA : Nat :=
  1079550984010321617061944982128822801677952903946337593724180313454694531

@[expose] noncomputable def GAI : Nat :=
  620590544519954183815691653192309756324906111630682346636640081585131651

end CertificateChecks.Perm3018

end
