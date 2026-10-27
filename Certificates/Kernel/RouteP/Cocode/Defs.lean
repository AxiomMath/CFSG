module

public import Certificates.Kernel.RouteP.Data.Obj
public import Certificates.Data.RouteP.Cocode

public section

namespace CFSG.KD.RouteP

open CFSG.KC CFSG.KC.RouteP CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

@[expose] def cl (l : Int) : Int :=
  if l = 1 then -54 else if l = -1 then 54 else if l = 2 then -58 else if l = -2 then 58
  else if 3 ≤ l then -(2 * l + 26) else 2 * (-l) + 26

@[expose] def invW (w : List Int) : List Int := w.reverse.map fun l => -l

@[expose] def cwT (i : Nat) : List Int :=
  if i < 11 then [1, (i : Int) + 3, -1] ++ invW (epsWord conjACols[i]!)
  else if i < 22 then [2, ((i - 11 : Nat) : Int) + 3, -2] ++ invW (epsWord conjBCols[i - 11]!)
  else (relLetters ())[i - 22]! ++ invW (epsWord relEps[i - 22]!)

@[expose] def cw (i : Nat) : List Int := (cwT i).map cl

@[expose] noncomputable def ck (g : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (idKOK NWO KAO KBO (cw (Nat.div g 20)))
    (idOK NWO (cw (Nat.div g 20)) (Nat.mod g 20)) (Nat.blt (Nat.mod g 20) 19)

@[expose] noncomputable def nk (j : Nat) : Bool :=
  andB (CFSG.KC.Fi24Net.netOK (NWO j)) (kapOK KAO KBO j)

end CFSG.KD.RouteP

end
