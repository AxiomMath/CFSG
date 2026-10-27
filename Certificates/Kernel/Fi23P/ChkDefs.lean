module

public import Certificates.Data.Kernel.Fi23P.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23P.Tabs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23P

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23P CFSG.KD.Fi23K

@[expose] noncomputable def rtP (c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 4777, nIf(Nat.beq c (nat_lit 1), nat_lit 16688, nat_lit 0))

@[expose] noncomputable def offP (c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0, nIf(Nat.beq c (nat_lit 1), nat_lit 255,
    nIf(Nat.beq c (nat_lit 2), nat_lit 13311, nat_lit 31671)))

@[expose] noncomputable def TG (k x : Nat) : Nat := tb G k x

@[expose] noncomputable def labP (x : Nat) : Nat := Nat.land (tb L (nat_lit 0) x) (nat_lit 3)
@[expose] noncomputable def genP (x : Nat) : Nat := Nat.shiftRight (tb L (nat_lit 0) x) (nat_lit 2)
@[expose] noncomputable def parP (x : Nat) : Nat := tb L (nat_lit 1) x
@[expose] noncomputable def posP (x : Nat) : Nat := tb L (nat_lit 2) x
@[expose] noncomputable def ptsP (x : Nat) : Nat := tb L (nat_lit 3) x
@[expose] noncomputable def depP (x : Nat) : Nat := tb L (nat_lit 4) x

@[expose] noncomputable def bPt (y : Nat) : Bool :=
  bAnd(bfsAt TG rtP offP labP genP parP posP ptsP y, depAt rtP labP parP depP y)

@[expose] noncomputable def bSl (s : Nat) : Bool :=
  allN (nat_lit 2048) fun i => strictB (Nat.add (Nat.mul s (nat_lit 2048)) i) fun y =>
    bIf(Nat.blt y (nat_lit 31671), bPt y, true)

@[expose] noncomputable def wS (t x : Nat) : Nat :=
  wR G (tb L (nat_lit 9)) (tb L (nat_lit 10) (Nat.mul (nat_lit 2) t))
    (tb L (nat_lit 10) (Nat.succ (Nat.mul (nat_lit 2) t))) x

@[expose] noncomputable def baseP (c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0, nIf(Nat.beq c (nat_lit 1), nat_lit 7,
    nIf(Nat.beq c (nat_lit 2), nat_lit 11, nat_lit 14)))

@[expose] noncomputable def sPt (y : Nat) : Bool :=
  strictB (labP y) fun c => bIf(Nat.beq y (rtP c), true, strictB (tb L (nat_lit 8) y) fun t =>
    bAnd(Nat.ble (baseP c) t, bAnd(Nat.blt t (baseP (Nat.succ c)),
      Bool.not (Nat.beq (wS t y) y))))

@[expose] noncomputable def sSl (s : Nat) : Bool :=
  allN (nat_lit 2048) fun i => strictB (Nat.add (Nat.mul s (nat_lit 2048)) i) fun y =>
    bIf(Nat.blt y (nat_lit 31671), sPt y, true)

end CFSG.KD.Fi23P

end
