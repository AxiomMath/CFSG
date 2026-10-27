module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.RouteP.Data.Pres
public import Certificates.Kernel.RouteP.Data.Obj
public import Certificates.Data.Kernel.RouteP.Ronan

#kc_repo #kc_ktree CFSG.KD.RouteP RN "Certificates/Kernel/RouteP/Ronan/data/ronan.bin" 65536 4 36765696 6692098348386030276

#kc_repo #kc_ktree CFSG.KD.RouteP RE "Certificates/Kernel/RouteP/Ronan/data/ronanent.bin" 16 4 2896 8172254275375621113

public section

namespace CFSG.KD.RouteP

@[expose] def rLo (g : Nat) : Nat := [0, 7, 26, 71, 105, 149, 181].getD g 0

@[expose] noncomputable def NWC (j l : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 58), NWO j l, NWP (Nat.sub j (nat_lit 58)) l)

@[expose] noncomputable def KAC (j : Nat) : Nat := NWC j (nat_lit 37)

@[expose] noncomputable def KBC (j : Nat) : Nat := NWC j (nat_lit 38)

open CFSG.KC.RouteP in
@[expose] noncomputable def baseCk (i : Nat) : Bool :=
  baseOK NWP KAP KBP [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] RN i

open CFSG.KC.RouteP in
@[expose] noncomputable def entCk (e : Nat) : Bool := entOK NWP KAP KBP RN RE e

open CFSG.KC.RouteP in
@[expose] noncomputable def grpCk (g : Nat) : Bool := grpOK RN RE g (rLo g) (rLo (g + 1))

end CFSG.KD.RouteP

end
