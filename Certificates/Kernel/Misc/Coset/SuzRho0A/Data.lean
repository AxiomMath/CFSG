module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import CFSG.Certificates.Kernel.Bounds.Load
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz

public section

#kc_blocked CFSG.KAct.SuzRho0.A include_bytes "data/SuzRho0.a" 8 4 65535 149688 16124372189297829896
#kc_blocked CFSG.KAct.SuzRho0.B include_bytes "data/SuzRho0.b" 8 4 65535 363528 13415031125757176934

namespace CFSG.KAct.SuzRho0

#kc_repo #kc_json_gz CFSG.KAct.SuzRho0
  "Certificates/Kernel/Misc/Coset/SuzRho0A/data/Data.json.gz" 1156 8268641448724670701
  (R : List (List Nat)) (W : List (List Nat)) (M : List (List Nat))

end CFSG.KAct.SuzRho0

end
