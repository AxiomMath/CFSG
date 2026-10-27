module

public import Certificates.Data.Kernel.Fi23R.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeKleinInputs

public section

namespace CFSG.KD.Fi23Klein

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

@[expose] def rW (w : List Nat) : List Nat := w.map (Nat.add (nat_lit 52))

@[expose] noncomputable def fxV (w : List Nat) (x : Nat) : Bool := Nat.beq (wv G w x) x

@[expose] noncomputable def baseV (w : List Nat) : Bool := allN (nat_lit 6) (fxV w)

@[expose] noncomputable def yK (w : List Nat) (o : Nat) (fx : List Nat) : Bool :=
  baseV (powW o (rW w)) && !baseV (rW w) && fx.all (fxV (rW w))

@[expose] noncomputable def kleinK : Bool :=
  allN (nat_lit 3) (fun i => allN (nat_lit 3) fun j => Nat.beq i j ||
      Nat.beq (tA G kleinPts[i]! kleinPts[j]!) kleinPts[j]!) &&
    allN (nat_lit 5) (fun k => yK kleinWords[k]! kleinOrders[k]! kleinFix[k]!) &&
    allN (nat_lit 3) (fun i => fxV (rW kleinZ) kleinPts[i]!)

end CFSG.KD.Fi23Klein

end
