module

public import Certificates.Data.Kernel.TwoNodeSmall.WitK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.TNS708603 "Certificates/Kernel/TwoNodeSmall/data/wk.json.gz"
  1895248 1976498242090500598
  (w8 : List (List CFSG.TwoNodeSmall.WitK.Rec)) (w9 : List (List CFSG.TwoNodeSmall.WitK.Rec))
  (w9m : List (List CFSG.TwoNodeSmall.WitK.Rec))

namespace CFSG.KD.TNS708603

open CFSG.TwoNodeSmall.WitK

@[expose] noncomputable def c8 (i : Nat) : Bool := chunkK 6 3 (blk8 (i / 3)) (w8.getD (i / 3) []) (i % 3)

@[expose] noncomputable def c9 (i : Nat) : Bool :=
  chunkK 18 3 (blk9 (i / 3)) (w9.getD (i / 3) []) (i % 3)

@[expose] noncomputable def c9m (i : Nat) : Bool :=
  chunkK 6 3 (blk9m (i / 3)) (w9m.getD (i / 3) []) (i % 3)

end CFSG.KD.TNS708603

end
