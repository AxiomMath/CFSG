module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import CFSG.Certificates.Kernel.Bounds.Load
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_blocked CFSG.KAct.XTitsP.A include_bytes "data/XTitsP.act" 8 4 65535 35100 10963829966054752883

namespace CFSG.KAct.XTitsP

#kc_repo #kc_json_gz CFSG.KAct.XTitsP
  "Certificates/Kernel/Misc/Coset/XTitsPA/data/Data.json.gz" 1060 7893061697015589199
  (rels : List (List Nat))

end CFSG.KAct.XTitsP

end
