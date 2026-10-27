module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.ONOut.Data
public import Certificates.Data.Kernel.Spor.WordProg

public section

#kc_repo #kc_ktree CFSG.KD.ONOut MT1 "Certificates/Kernel/ONOut/data/mats1.bin" 5929 4 112651 7229590398262676269
#kc_repo #kc_json_family_gz CFSG.KD.ONOut "Certificates/Kernel/ONOut/data/lists1.json.gz" 6229 2918490483332359432
  (PS : List Nat) (WC : List Nat)

namespace CFSG.KD.ONOut

@[expose] noncomputable def RB (k : Nat) : Nat :=
  [nat_lit 0, MT 0, MT 1, MT1 0, MT1 1, MT1 2, MT1 3, MT1 4, MT 2, MT1 5, MT1 6, MT1 7, MT1 8,
    MT1 9, MT1 10, MT1 11, MT1 12].getD k (nat_lit 0)

@[expose] noncomputable def RS (k : Nat) : Nat :=
  [MT1 13, MT1 14, MT1 14, MT1 15, MT1 15, MT1 16, MT1 16, MT1 17, MT1 17, MT1 18, MT1 18, MT1 0,
    MT1 1, MT1 2, MT1 3, MT1 4].getD k (nat_lit 0)

end CFSG.KD.ONOut

#kc_listDispatch CFSG.KD.ONOut PS PS 16
#kc_listDispatch CFSG.KD.ONOut WC WC 16

end
