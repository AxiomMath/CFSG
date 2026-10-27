module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24FiveK.Data
public import Certificates.Data.Kernel.Spor.Fi24FiveKQ

#kc_repo #kc_json_gz CFSG.KD.Fi24FiveK.DQ "Certificates/Kernel/Sporadic/Fi24FiveK/data/fiveq.json.gz"
  783 10675364746736288747
  (Q : List (List Nat))

public section

namespace CFSG.KD.Fi24FiveK

open CFSG.KC.Fi24FiveK

@[expose] noncomputable def blk (i : Nat) : Bool := blkOK E D.R DQ.Q 33 i

@[expose] noncomputable def prd : Bool := prodOK E DQ.Q 11

end CFSG.KD.Fi24FiveK

end
