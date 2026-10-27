module

public import Certificates.Data.Kernel.TwoNodeSmall.PosBK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.TNS708601 "Certificates/Kernel/TwoNodeSmall/data/bk.json.gz"
  12588410 8863199037434296174
  (rk : List (List CFSG.TwoNodeSmall.ExclK.Rec)) (os : List (List CFSG.TwoNodeSmall.PosBK.ORec))

namespace CFSG.KD.TNS708601

open CFSG.TwoNodeSmall.PosBK

@[expose] noncomputable def cg (g : Nat) : Bool := grpIdxB rk os g

@[expose] def oB : Nat := 12

@[expose] def nO : Nat := 153

@[expose] noncomputable def co (i : Nat) : Bool := ochunkB oB os i

@[expose] noncomputable def cn (_ : Nat) : Bool := Nat.beq (ochunks oB os).length nO

end CFSG.KD.TNS708601

end
