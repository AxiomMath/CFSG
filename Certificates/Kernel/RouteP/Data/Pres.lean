module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Data.Kernel.RouteP.Mono

#kc_repo #kc_ktree CFSG.KD.RouteP P
  ("Certificates/Kernel/RouteP/Data/data/pres.bin.0" 53673984 13967666688446863451)
  ("Certificates/Kernel/RouteP/Data/data/pres.bin.1" 53673984 6107814669045967685)
  65536 4 107347968 9739132385341089938

public section

namespace CFSG.KD.RouteP

@[expose] noncomputable def NWP (j l : Nat) : Nat := P (Nat.add (Nat.mul j (nat_lit 39)) l)

@[expose] noncomputable def KAP (j : Nat) : Nat := NWP j (nat_lit 37)

@[expose] noncomputable def KBP (j : Nat) : Nat := NWP j (nat_lit 38)

end CFSG.KD.RouteP

end
