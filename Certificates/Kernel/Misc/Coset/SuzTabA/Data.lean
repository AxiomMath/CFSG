module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import CFSG.Certificates.Kernel.Bounds.Load
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_blocked CFSG.KAct.SuzTab.A include_bytes "data/SuzTab.act" 8 4 65535 64152 8909152627585324414

namespace CFSG.KAct.SuzTab

#kc_repo #kc_json_gz CFSG.KAct.SuzTab
  "Certificates/Kernel/Misc/Coset/SuzTabA/data/Data.json.gz" 5219 17158752284783105716
  (rels : List (List Nat))

end CFSG.KAct.SuzTab

end
