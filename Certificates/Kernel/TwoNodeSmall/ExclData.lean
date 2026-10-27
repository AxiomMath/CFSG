module

public import Certificates.Data.Kernel.TwoNodeSmall.ExclK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.TNS708602 "Certificates/Kernel/TwoNodeSmall/data/xk.json.gz"
  534369 13696346777465306488
  (cs : List (List (List Nat))) (rk : List (List CFSG.TwoNodeSmall.ExclK.Rec))

namespace CFSG.KD.TNS708602

open CFSG.TwoNodeSmall.ExclK

@[expose] noncomputable def cc (i : Nat) : Bool := csAt i (cs.getD i [])

@[expose] noncomputable def cg (g : Nat) : Bool := grpIdx cs rk g

end CFSG.KD.TNS708602

end
