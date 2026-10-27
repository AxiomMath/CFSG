module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import CFSG.Certificates.Kernel.Bounds.LoadGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz

public section

#kc_repo #kc_blocked_gz CFSG.KAct.PhanB3CT.A "Certificates/Kernel/PhanB3/data/B3CT.a.gz"
  8 4 65535 62720 5592078678960482652

#kc_repo #kc_json_gz CFSG.KAct.PhanB3CT "Certificates/Kernel/PhanB3/data/B3CTW.json.gz" 6862
  5990131563927022073 (RD : List (List Nat)) (RC : List (List Nat))

namespace CFSG.KAct.PhanB3CT

@[expose] def R : List (List Nat) :=
  [[6, 6, 6], [0, 0, 0, 0], [0, 4, 1, 5], [0, 5, 3, 4, 3], [0, 6, 1, 6, 5], [2, 6, 3, 6, 2, 7],
   [10, 10, 10], [5, 9, 4, 8], [8, 8, 8, 8], [4, 4, 4, 4], [5, 11, 4, 11, 8], [8, 4, 6, 9, 5, 7],
   [6, 4, 9, 7, 5, 8], [4, 7, 4, 7, 4, 7], [10, 6, 11, 4, 7, 10, 7, 11, 6, 5],
   [10, 7, 11, 7, 10, 7, 11, 6, 10, 6, 11, 6], [8, 10, 6, 11, 7, 11, 9, 7, 4, 10, 6, 11, 7, 4, 4],
   [0, 8, 1, 9], [0, 10, 1, 11], [2, 8, 3, 9], [2, 10, 3, 11], [13, 11, 9, 10, 4, 11, 8, 10],
   [15, 11, 9, 10, 6, 11, 8, 10], [4, 12, 5, 13], [4, 14, 5, 15], [6, 12, 7, 13], [6, 14, 7, 15],
   [0, 6, 2, 5, 7, 14, 2, 14, 0, 6, 2, 5, 7, 14, 2, 14],
   [0, 3, 5, 6, 3, 1, 15, 2, 6, 2, 4, 4, 15, 2, 6, 2, 15]]

end CFSG.KAct.PhanB3CT

end
