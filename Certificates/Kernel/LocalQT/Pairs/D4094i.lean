module

public import Certificates.Data.Kernel.LocalQT.PairsH
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000

#kc_repo #kc_json_gz CFSG.KD.LQT.M24Idx
  "Certificates/Kernel/LocalQT/Pairs/data/d4094i.json.gz" 376019 5366472374558716292
  (I0 : List Nat) (I1 : List Nat) (I2 : List Nat) (I3 : List Nat) (I4 : List Nat) (I5 : List Nat)
  (I6 : List Nat) (I7 : List Nat)

public section

namespace CFSG.KD.LQT.M24Idx

@[expose] noncomputable def I : List (List Nat) :=
  [I0, I1, I2, I3, I4, I5, I6, I7]

end CFSG.KD.LQT.M24Idx

end
