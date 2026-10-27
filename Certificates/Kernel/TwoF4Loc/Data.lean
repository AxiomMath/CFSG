module

public import CFSG.Certificates.Kernel.Common.JsonGz
public import Certificates.Kernel.Misc.PackJson
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.TwoF4Loc "Certificates/Kernel/TwoF4Loc/data/loc.json.gz" 544972
  940712905835300198 (fx : List Nat) (cl : List Nat) (ch : List (List (Nat × Nat)))

#kc_repo #kmisc_json_pack CFSG.KD.TwoF4Loc "Certificates/Kernel/TwoF4Loc/data/loc.json.gz"
  544972 940712905835300198 (tT TT 11) (cT TC 11) (qT TQ 11) (zz TZ 11) (mT TM 11) (mI TMI 11) (wT TW 11)
  (wI TWI 11)

namespace CFSG.KD.TwoF4Loc

@[expose] def cws : List String := ["6", "4", "40", "263175352", "12153533733", "62"]

end CFSG.KD.TwoF4Loc

end
