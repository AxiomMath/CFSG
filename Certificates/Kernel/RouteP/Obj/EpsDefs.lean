module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.RouteP.Data.Obj
public import Certificates.Data.Kernel.Spor.Fi24NetPt
public import CFSG.Certificates.Kernel.RouteP.EpsTree
public import Mathlib

#kc_repo #kc_ktree CFSG.KD.RouteP EPD "Certificates/Kernel/RouteP/Obj/data/eps.bin" 4096 4 16384 11204058601439063724

public section

namespace CFSG.KD.RouteP

open CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

@[expose] def kvB (a b q : Nat) : Nat :=
  (bif a.testBit q then 1 else 0) + (bif b.testBit q then 2 else 0)

@[expose] noncomputable def ptT (r x : Nat) : Nat :=
  (fun q => 3 * q + (x % 3 + (2 * kvB (KAO r) (KBO r) q) % 3) % 3) (CFSG.KC.Fi24NetPt.ptR (NWO r) (x / 3))

@[expose] noncomputable def epsK : Nat → Nat → Nat → Nat
  | 0, _, p => p
  | f + 1, k, p => if k = 0 then p else ptT (epsReg (lowBit k)) (epsK f (k - 1 <<< lowBit k) p)

@[expose] noncomputable def epsCode (k : Nat) : Nat := 920808 * epsK k k 3 + epsK k k 6

@[expose] noncomputable def epR (i : Nat) : Nat :=
  fld(EPD (Nat.shiftRight i (nat_lit 9)), Nat.mul (Nat.land i (nat_lit 511)) (nat_lit 64),
    nat_lit 18446744073709551615)

@[expose] noncomputable def epC (i : Nat) : Nat := Nat.land (epR i) (nat_lit 1099511627775)

@[expose] noncomputable def epPos (k : Nat) : Nat := Nat.land (Nat.shiftRight (epR k) (nat_lit 40)) (nat_lit 2047)

@[expose] noncomputable def epInv (i : Nat) : Nat := Nat.land (Nat.shiftRight (epR i) (nat_lit 51)) (nat_lit 2047)

@[expose] noncomputable def epsCk (k : Nat) : Bool :=
  andB (Nat.beq (epsCode k) (epC (epPos k))) (Nat.beq (epInv (epPos k)) k)

@[expose] noncomputable def epsSorted (i : Nat) : Bool := Nat.blt (epC i) (epC (Nat.add i 1))

end CFSG.KD.RouteP

end
