module

public import Certificates.Kernel.HNMult.Data
public import Certificates.Data.Kernel.LaneChain
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KD.HNMChain "Certificates/Kernel/HNMult/data/hnchain.json.gz" 5700
  15750444191647441069 (R : List (List Nat)) (B : List (List Nat)) (G : List (List Nat))
  (T : List (List Nat)) (N : List Nat)

public section

namespace CFSG.KD.HNMChain

open CFSG.KD.HNMult

@[expose] noncomputable def M₀ : List Nat :=
  [RB 24, RB 23, RB 22, RB 21, RB 20, RB 11, RB 10, RB 9, RB 8, RB 7]

theorem chain_ok : CFSG.KC.LaneChain.chainOK mul vld (nat_lit 1729) R B G T M₀
    (nat_lit 88704000) = true := by
  quickRfl

end CFSG.KD.HNMChain

end
