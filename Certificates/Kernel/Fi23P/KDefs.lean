module

public import Certificates.Kernel.Fi23P.ChkDefs
public import Certificates.Data.CFSGNative.MonsterAxis.Fi23Sp8

public section

namespace CFSG.KD.Fi23P

open CFSG.Sporadic.Th.Native CFSG.Monster.Existence.Fi23Sp8.Native CFSG.KC.Fi23K CFSG.KD.Fi23K

@[expose] noncomputable def XK (k x : Nat) : Nat := if k < 10 ∧ x < 31671 then tb G k x else 0

@[expose] def zIdx (z : Int) : Nat := if 0 < z then (z - 1).toNat else (-z - 1).toNat

@[expose] noncomputable def wK (w : List Int) (q : Nat) : Nat := w.foldr (fun z x => XK (zIdx z) x) q

@[expose] noncomputable def labG (x : Nat) : Nat := if x < 31671 then labP x else 0
@[expose] noncomputable def parG (x : Nat) : Nat := if x < 31671 then parP x else 0
@[expose] noncomputable def genG (x : Nat) : Nat := if x < 31671 then genP x else 0

@[expose] def rootsA : Array Nat := #[4777, 16688, 0]

@[expose] noncomputable def pathF (r : Nat) : Nat → Nat → List Int
  | 0, _ => []
  | f + 1, p => if p == r then [] else ((genG p + 1 : Nat) : Int) :: pathF r f (parG p)

@[expose] noncomputable def pathK (p : Nat) : List Int := pathF rootsA[labG p]! 100 p

@[expose] noncomputable def conjK (u : List Int) (q : Nat) : Nat := wK u (XK 0 (wK (invWord u) q))

@[expose] noncomputable def commK (p q : Nat) : Bool := conjK (pathK p) q == q

@[expose] noncomputable def sigL : List Nat := (List.range 255).map fun i => tb L 7 i

@[expose] def bLit : Array Nat := #[10, 636, 1309, 2632, 120, 664, 1575, 4713]

@[expose] noncomputable def vecG (p : Nat) : Nat := if p < 31671 ∧ labP p = 0 then tb L 5 p else 0

@[expose] noncomputable def ptA : Array Nat := ((List.range 256).map fun v => tb L 6 v).toArray

end CFSG.KD.Fi23P

end
