module

public import Certificates.Data.Kernel.Fi23R.Defs
public import Certificates.Kernel.Fi23K.Tabs

public section

namespace CFSG.KD.Fi23S

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K

@[expose] def SP : List Nat := [0, 4953, 15723, 20053, 6049, 8308, 8379, 145, 17454, 5528, 14172]

@[expose] noncomputable def eS (i : Nat) : Nat := Nat.add (nat_lit 128) (List.getD SP i (nat_lit 0))

@[expose] noncomputable def w4 : List Nat := [eS 6, eS 4, eS 2, eS 0]
@[expose] noncomputable def w6 : List Nat := eS 10 :: eS 8 :: w4

@[expose] def wR4 : List Nat := [39, 41, 167, 129, 43, 40, 39]
@[expose] def wR6 : List Nat := [41, 39, 41, 129, 43, 40, 39, 40]

@[expose] noncomputable def g4 : List Nat := powW 6 (w4 ++ wR4)
@[expose] noncomputable def g6 : List Nat := powW 2 (w6 ++ wR6)

@[expose] noncomputable def s12K : Bool :=
  bAnd(allN (nat_lit 10) (fun i => eqB G [eS i, eS (Nat.succ i), eS i]
    [eS (Nat.succ i), eS i, eS (Nat.succ i)]),
  bAnd(allN (nat_lit 11) (fun i => allN (nat_lit 11) fun j =>
    bIf(Nat.blt j (Nat.add i (nat_lit 2)), true, eqB G [eS j, eS i] [eS i, eS j])),
  bAnd(eqB G (w4 ++ w4) [], bAnd(eqB G (w6 ++ w6) [],
  bAnd(Bool.not (Nat.beq (wa G w4 (nat_lit 2)) (nat_lit 2)),
  bAnd(Bool.not (Nat.beq (wa G w6 (nat_lit 2)) (nat_lit 2)),
  bAnd(eqB G (invW g4 ++ wR4 ++ g4) w4, eqB G (invW g6 ++ wR6 ++ g6) w6)))))))

@[expose] noncomputable def negG : Bool := Bool.not (eqB G (invW g6 ++ wR4 ++ g6) w4)

end CFSG.KD.Fi23S

end
