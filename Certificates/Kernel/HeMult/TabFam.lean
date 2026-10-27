module

public import Certificates.Kernel.HeMult.TabData
public import Certificates.Kernel.HeTab.Data
public import Certificates.Kernel.HeOrb.Data
public import Certificates.Data.Kernel.HeMultK

public section

namespace CFSG.KD.HeMult

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.KC.HeMult CFSG.KD.HeOrb CFSG.KD.HeTab
  CFSG.Sporadic.Recognition.HeMultiplier

@[expose] noncomputable def slice (p : Nat → Bool) (c : Nat) : Bool :=
  allN (nat_lit 1000) fun d => strictB (Nat.add (Nat.mul (nat_lit 1000) c) d) fun x =>
    bIf(Nat.blt x (nat_lit 8330), p x, true)

@[expose] noncomputable def famC (c : Nat) : Bool := slice (cK AL BE BI CT cW) c

@[expose] noncomputable def famG (c : Nat) : Bool :=
  slice (fun x => bAnd(powK AL CT Wu U Ui uAC uExp x, bAnd(powK AL CT Wv V Vi vAC vExp x,
    bAnd(powK AL CT Ws S Si sAC sExp x, tK AL BE BI T Ti tAB x)))) c

@[expose] noncomputable def famR (c : Nat) : Bool :=
  slice (relK AL BE U V S T Ui Vi Si Ti heTabRels heSurjA heSurjB) c

@[expose] noncomputable def famR0 (c : Nat) : Bool := famR c
@[expose] noncomputable def famR1 (c : Nat) : Bool := famR (Nat.add c (nat_lit 3))
@[expose] noncomputable def famR2 (c : Nat) : Bool := famR (Nat.add c (nat_lit 6))

end CFSG.KD.HeMult

end
