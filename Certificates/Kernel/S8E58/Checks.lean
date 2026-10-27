module

public import Certificates.Data.Kernel.S8E58K
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KD.S8E58 "Certificates/Kernel/S8E58/data/t.json.gz" 655907
  3122014345145363440
  (CM : Nat) (MT : Nat) (FX : Nat) (R : Nat) (W : Nat)

open CFSG.KC.S8E58K CFSG.KD.S8E58

#kc_each CFSG.KD.S8E58 ch7158_k34_ (fun i => k34K CM MT FX R W i) 0 43
