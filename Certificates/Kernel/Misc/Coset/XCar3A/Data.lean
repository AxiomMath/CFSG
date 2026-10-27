module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import CFSG.Certificates.Kernel.Bounds.Load
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_blocked CFSG.KAct.XCar3.A include_bytes "data/XCar3.act" 8 4 65535 1440 6261800842266485

namespace CFSG.KAct.XCar3

#kc_repo #kc_json_gz CFSG.KAct.XCar3
  "Certificates/Kernel/Misc/Coset/XCar3A/data/Data.json.gz" 442 2560641818538432258
  (rels : List (List Nat))

end CFSG.KAct.XCar3

end
