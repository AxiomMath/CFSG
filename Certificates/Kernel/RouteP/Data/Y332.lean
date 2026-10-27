module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.RouteP.Data.Obj

#kc_repo #kc_ktree CFSG.KD.RouteP Y
  ("Certificates/Kernel/RouteP/Data/data/y332.bin.0" 69861376 16883565373432672680)
  ("Certificates/Kernel/RouteP/Data/data/y332.bin.1" 69861376 2048193027623702495)
  ("Certificates/Kernel/RouteP/Data/data/y332.bin.2" 69861376 11329564832455484232)
  65536 4 209584128 11060492899470799785

public section

namespace CFSG.KD.RouteP

@[expose] noncomputable def NWY (j l : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 30), NWO j l, Y (Nat.add (Nat.mul (Nat.sub j (nat_lit 30)) (nat_lit 39)) l))

@[expose] noncomputable def KAY (j : Nat) : Nat := NWY j (nat_lit 37)

@[expose] noncomputable def KBY (j : Nat) : Nat := NWY j (nat_lit 38)

end CFSG.KD.RouteP

end
