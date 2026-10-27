module

public import Certificates.Data.Kernel.S8F28K
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KD.S8F28 "Certificates/Kernel/S8F28/data/t.json.gz" 6060
  16928309176159734382
  (CM : Nat) (MT : Nat) (FMK : Nat)

open CFSG.KC.S8F28K CFSG.KD.S8F28

#kc_each CFSG.KD.S8F28 ch7218_c2 (fun _ => c2K CM MT FMK) 0 1

#kc_each CFSG.KD.S8F28 ch7218_c3_ (fun i => c3K CM MT FMK i) 0 43

#kc_each CFSG.KD.S8F28 ch7218_c4_ (fun i => c4K CM MT FMK i) 0 43
