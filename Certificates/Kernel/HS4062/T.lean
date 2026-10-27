module

public import Certificates.Kernel.HS4062.D
public import Certificates.Data.Kernel.Kc3E16T
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.HS4062

@[expose] noncomputable def NB (i : Nat) : List Nat := J.NB.getD i []

@[expose] noncomputable def FL (i : Nat) : List Nat := J.FL.getD i []

@[expose] noncomputable def FR (r : Nat) : List Nat := J.FR.getD r []

@[expose] noncomputable def EL (k : Nat) : List Nat := J.EL.getD k []

@[expose] noncomputable def PI (t : Nat) : List Nat := J.PI.getD t []

@[expose] def pairsOf : List Nat → List (Nat × Nat)
  | a :: b :: l => (a, b) :: pairsOf l
  | _ => []

@[expose] noncomputable def progX : List (Nat × Nat) := pairsOf XP

@[expose] noncomputable def ERec (k : Nat) : Nat :=
  fld(ER (Nat.shiftRight k (nat_lit 6)), Nat.mul (nat_lit 98) (Nat.land k (nat_lit 63)),
    nat_lit 316912650057057350374175801343)

@[expose] noncomputable def eu (k : Nat) : Nat := Nat.land (ERec k) (nat_lit 255)
@[expose] noncomputable def ev (k : Nat) : Nat := fld(ERec k, nat_lit 8, nat_lit 255)
@[expose] noncomputable def tg (c k : Nat) : Nat :=
  fld(ERec k, Nat.add (nat_lit 16) (Nat.mul (nat_lit 9) c), nat_lit 511)
@[expose] noncomputable def iv (k : Nat) : Nat := fld(ERec k, nat_lit 43, nat_lit 127)
@[expose] noncomputable def ky (k : Nat) : Nat := fld(ERec k, nat_lit 50, nat_lit 281474976710655)

@[expose] noncomputable def vu (i : Nat) : Nat := Nat.land (VR i) (nat_lit 255)
@[expose] noncomputable def vv (i : Nat) : Nat := fld(VR i, nat_lit 8, nat_lit 255)
@[expose] noncomputable def kv (i : Nat) : Nat := fld(VR i, nat_lit 16, nat_lit 511)
@[expose] noncomputable def rt (i : Nat) : Nat := fld(VR i, nat_lit 25, nat_lit 15)
@[expose] noncomputable def cj (i : Nat) : Nat := fld(VR i, nat_lit 29, nat_lit 511)

@[expose] noncomputable def pr (i j : Nat) : Nat := fld(PR i, Nat.mul (nat_lit 7) j, nat_lit 127)
@[expose] noncomputable def ct (i j : Nat) : Nat := fld(CR i, Nat.mul (nat_lit 6) j, nat_lit 63)

@[expose] def B : List Nat := [0, 1, 2, 3]

@[expose] noncomputable def TA : Array Nat :=
  ((List.range 3850).map (CFSG.KC.Enum.pg 12 4095 (TF 0))).toArray

@[expose] noncomputable def TB : Array Nat :=
  ((List.range 3850).map (CFSG.KC.Enum.pg 12 4095 (TF 1))).toArray

end CFSG.KD.HS4062

end
