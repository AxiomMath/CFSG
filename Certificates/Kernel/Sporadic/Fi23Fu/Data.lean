module

import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi23Br.Data

#kc_repo #kc_nat_items_gz CFSG.KD.Fi23Fu "Certificates/Kernel/Sporadic/Fi23Fu/data/gens.items.gz" 2112368 270297859131404279
    (G 0 12) (Gi 0 12)

public noncomputable section

namespace CFSG.KD.Fi23Fu

open CFSG.KD.BrFi23 (MT)

@[expose] def RF (k : Nat) : Nat :=
  [nat_lit 0, MT 0, MT 1, MT 2, MT 3, MT 4, MT 5, MT 6, MT 7, MT 8, MT 9, MT 10, MT 11,
    G0, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11,
    MT 0, MT 1, MT 2, MT 3, MT 4, MT 5, MT 6, MT 7, MT 8, MT 9, MT 10, MT 12,
    Gi0, Gi1, Gi2, Gi3, Gi4, Gi5, Gi6, Gi7, Gi8, Gi9, Gi10, Gi11].getD k (nat_lit 0)

end CFSG.KD.Fi23Fu

end
