module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.RouteP.Data.Pres

#kc_repo #kc_ktree CFSG.KD.RouteP PRel3 "Certificates/Kernel/RouteP/Data/data/presU.bin"
  65536 4 2555904 18067903694215165114

public section

namespace CFSG.KD.RouteP

@[expose] noncomputable def NWU3 (j l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (NWP j l) (PRel3 l) (Nat.beq j (nat_lit 42))

@[expose] noncomputable def KAU3 (j : Nat) : Nat := NWU3 j (nat_lit 37)

@[expose] noncomputable def KBU3 (j : Nat) : Nat := NWU3 j (nat_lit 38)

end CFSG.KD.RouteP

end
