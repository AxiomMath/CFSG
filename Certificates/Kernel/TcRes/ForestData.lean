module

public import Certificates.Data.Kernel.TcRes.Forest
public import Certificates.Kernel.TcRes.Data
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_ktree_gz CFSG.KD.TcRes.C1 LF "Certificates/Kernel/TcRes/data/c1forest.bin.gz"
  536 4 434160 8860646953230018340

#kc_repo #kc_nat_items_gz CFSG.KD.TcRes.C1 "Certificates/Kernel/TcRes/data/c1reps.bin.gz"
  532 8325624390888456230 REPS WRD

namespace CFSG.KD.TcRes

open CFSG.TcRes.TK

@[expose] noncomputable def C1.leaf (L : Nat) : Bool := leafOK E6.RT C1.LF C1.REPS L

@[expose] noncomputable def C1.rep (k : Nat) : Bool := repOK E6.RT C1.REPS C1.WRD k

end CFSG.KD.TcRes

end
