module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import CFSG.Certificates.Kernel.Bounds.Load
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_blocked CFSG.KAct.RuRho.A include_bytes "data/RuRho.a" 8 4 65535 194880 3808388335299442022
#kc_blocked CFSG.KAct.RuRho.B include_bytes "data/RuRho.b" 8 4 65535 389760 13672079227877711382

namespace CFSG.KAct.RuRho

#kc_repo #kc_json_gz CFSG.KAct.RuRho
  "Certificates/Kernel/Misc/Coset/RuRhoA/data/Data.json.gz" 864 13561344229732552612
  (R : List (List Nat)) (W : List (List Nat)) (M : List (List Nat))

end CFSG.KAct.RuRho

end
