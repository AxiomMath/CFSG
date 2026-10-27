module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import CFSG.Certificates.Kernel.Bounds.Load
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz

public section

#kc_blocked CFSG.KAct.XQP.A include_bytes "data/XQP.act" 8 4 65535 1944 16217183037936777809

namespace CFSG.KAct.XQP

#kc_repo #kc_json_gz CFSG.KAct.XQP
  "Certificates/Kernel/Misc/Coset/XQP/data/Data.json.gz" 8775 8089638243236851015
  (rels : List (List Nat)) (ws : List (List Nat)) (base : List Nat) (ord : List Nat)

end CFSG.KAct.XQP

end
