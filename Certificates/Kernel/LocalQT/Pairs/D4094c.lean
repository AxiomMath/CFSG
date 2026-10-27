module

public import Certificates.Data.Kernel.LocalQT.PairsH
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000

open CFSG.KC.LQT.PH in
#kc_repo #kc_json_gz CFSG.KD.LQT.M24Class
  "Certificates/Kernel/LocalQT/Pairs/data/d4094c.json.gz" 583760 972118639148888001
  (B : List Blk) (T : List (List (Nat × Nat × Nat)))
