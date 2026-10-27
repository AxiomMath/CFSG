module

public import Certificates.Data.Kernel.LocalQT.PairsH
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000

open CFSG.KC.LQT.L in
#kc_repo #kc_json_gz CFSG.KD.LQT.M24Chain
  "Certificates/Kernel/LocalQT/Pairs/data/d4094.json.gz" 13342 17056877756615649569
  (CS : List Lvl) (WS : List (List (List Nat))) (CK1 : List Lvl) (WK1 : List (List (List Nat)))
  (CT0 : List Lvl) (WT0 : List (List (List Nat))) (CK2 : List Lvl) (WK2 : List (List (List Nat)))
  (CQ1 : List Lvl) (WQ1 : List (List (List Nat))) (CA2 : List Lvl) (WA2 : List (List (List Nat)))
