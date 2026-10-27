module

public import Certificates.Kernel.HN1408.Gens
public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH

@[expose] noncomputable def L (l : Nat) : Nat := H8.F (l - 1)

@[expose] noncomputable def idK : Nat := pidn 1408 11

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1408 11 (mask 11) p q

@[expose] noncomputable def WK (wd : List Nat) : Nat := wfoldK 1408 11 (mask 11) L wd idK

@[expose] noncomputable def pt (p i : Nat) : Nat := pg 11 (mask 11) p i

@[expose] def lettersOK (wd : List Nat) : Bool := wd.all fun l => 1 ≤ l && l ≤ 7

@[expose] noncomputable def involK (p : Nat) : Bool :=
  bAnd(Nat.beq (pc p p) idK, bIf(Nat.beq p idK, false, true))

@[expose] noncomputable def commP (p q : Nat) : Bool := Nat.beq (pc p q) (pc q p)

@[expose] noncomputable def halvesK (p : Nat) : Bool :=
  allN 704 fun k => bAnd(Nat.blt (pt p k) 704, Nat.ble 704 (pt p (704 + k)))

end CFSG.KD.HN1408

end
