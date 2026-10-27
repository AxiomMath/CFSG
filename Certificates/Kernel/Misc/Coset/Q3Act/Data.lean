module

public import Certificates.Data.Kernel.Misc.Coset.CovAct
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KAct.Q3

set_option maxRecDepth 100000

#kc_repo #kc_blocked_root CFSG.KAct.Q3.A "Certificates/Kernel/Misc/Coset/Q3Act/data/act291372.bin"
  10 5 4294967295 30693600 12495537587577017335

#kc_repo #kc_json_gz CFSG.KAct.Q3
  "Certificates/Kernel/Misc/Coset/Q3Act/data/act291372.json.gz" 3993 5356152074493403239
  (N : Nat) (L : Nat) (zs : List Nat) (mac : List (List Nat)) (chk : List (List Nat × Nat))
  (hint : List (Nat × Nat × Nat))

@[expose] noncomputable def blk (k : Nat) : Bool :=
  CFSG.KC.MiscCoset.Act.allR (Nat.mul k 72) 72
    (CFSG.KC.MiscCoset.CovAct.cpOK A 3 306936 11 25 mac chk)

end CFSG.KAct.Q3
