module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Data.Kernel.RouteP.Mono

#kc_repo #kc_ktree CFSG.KD.RouteP O
  ("Certificates/Kernel/RouteP/Data/data/obj.bin.0" 74121216 18224417205916435755)
  ("Certificates/Kernel/RouteP/Data/data/obj.bin.1" 74121216 3459199743933539662)
  65536 4 148242432 13169355200557728596

public section

namespace CFSG.KD.RouteP

@[expose] noncomputable def NWO (j l : Nat) : Nat := O (Nat.add (Nat.mul j (nat_lit 39)) l)

@[expose] noncomputable def KAO (j : Nat) : Nat := NWO j (nat_lit 37)

@[expose] noncomputable def KBO (j : Nat) : Nat := NWO j (nat_lit 38)

end CFSG.KD.RouteP

end
