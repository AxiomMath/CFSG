module

public import Certificates.Kernel.RouteP.Data.Obj
public import Certificates.Data.RouteP.Objects

public section

namespace CFSG.KD.RouteP

open CFSG.KC CFSG.KC.RouteP CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

@[expose] def oL (r : Nat) : Int := ((r + 1 : Nat) : Int)

@[expose] noncomputable def tck (b : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (ptOK NWO KAO KBO [oL tauReg] 0 1479)
    (ptOK NWO KAO KBO [oL tauReg] 1479 0) (Nat.beq b 0)

@[expose] noncomputable def idck (w : List Int) (k : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (idKOK NWO KAO KBO w) (idOK NWO w k) (Nat.blt k 19)

@[expose] noncomputable def invck (g : Nat) : Bool :=
  (fun j => idck [oL (epsReg j), oL (epsReg j)] (Nat.mod g 20)) (Nat.div g 20)

@[expose] noncomputable def commck (g : Nat) : Bool :=
  (fun n => (fun i j => Bool.rec (motive := fun _ => Bool) true
      (idck [oL (epsReg i), oL (epsReg j), -oL (epsReg i), -oL (epsReg j)] (Nat.mod g 20))
      (Nat.blt j i)) (Nat.div n 11) (Nat.mod n 11)) (Nat.div g 20)

@[expose] noncomputable def pck (g : Nat) : Bool :=
  (fun x => ptOK NWO KAO KBO [oL (epsReg (Nat.div g 24))] x x) (planeArr[Nat.mod g 24]!)

@[expose] noncomputable def abck (g : Nat) : Bool :=
  (fun i => Bool.rec (motive := fun _ => Bool)
    (ptOK NWO KAO KBO [oL bReg] (planeArr[planeBArr[i]!]!) (planeArr[i]!))
    (ptOK NWO KAO KBO [oL aReg] (planeArr[planeAArr[i]!]!) (planeArr[i]!)) (Nat.blt g 24))
    (Nat.mod g 24)

end CFSG.KD.RouteP

end
