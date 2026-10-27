module

public import Certificates.Data.Kernel.LocalQT.PairsH
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000

open CFSG.KC.LQT.PH in
#kc_repo #kc_json_gz CFSG.KD.LQT.M24Trio
  "Certificates/Kernel/LocalQT/Pairs/data/d4094t.json.gz" 135360 8318961009318950201
  (B : List Blk) (T : List (List (Nat × Nat × Nat)))
