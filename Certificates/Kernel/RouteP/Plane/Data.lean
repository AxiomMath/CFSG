module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.RouteP.Data.Obj

#kc_repo #kc_ktree CFSG.KD.RouteP PQ "Certificates/Kernel/RouteP/Plane/data/planegens.bin" 65536 4 7667712 5014758617544173350

public section

namespace CFSG.KD.RouteP

@[expose] noncomputable def NWQ (j l : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 58), NWO j l, PQ (Nat.add (Nat.mul (Nat.sub j (nat_lit 58)) (nat_lit 39)) l))

@[expose] noncomputable def KAQ (j : Nat) : Nat := NWQ j (nat_lit 37)

@[expose] noncomputable def KBQ (j : Nat) : Nat := NWQ j (nat_lit 38)

end CFSG.KD.RouteP

end
