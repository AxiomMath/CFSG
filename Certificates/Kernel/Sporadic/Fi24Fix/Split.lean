module

public import Certificates.Data.Kernel.Spor.Fi24Fix

public section

namespace CFSG.KC.Fi24Fix

theorem wordMul_append (mul : Nat → Nat → Nat) (RB : Nat → Nat) (p q : List Nat) (Y : Nat) :
    wordMul mul RB (p ++ q) Y = wordMul mul RB p (wordMul mul RB q Y) := by
  induction p with
  | nil => rfl
  | cons k p ih => exact congrArg (mul (RB k)) ih

theorem beq_wordMul_append {mul : Nat → Nat → Nat} {RB : Nat → Nat} {p q : List Nat} {Y M Z : Nat}
    (h1 : Nat.beq (wordMul mul RB q Y) M = true) (h2 : Nat.beq (wordMul mul RB p M) Z = true) :
    Nat.beq (wordMul mul RB (p ++ q) Y) Z = true := by
  rw [wordMul_append, Nat.eq_of_beq_eq_true h1]
  exact h2

theorem notB_beq_wordMul_append {mul : Nat → Nat → Nat} {RB : Nat → Nat} {p q : List Nat}
    {Y M Z : Nat} (h1 : Nat.beq (wordMul mul RB q Y) M = true)
    (h2 : CFSG.KC.Ord.notB (Nat.beq (wordMul mul RB p M) Z) = true) :
    CFSG.KC.Ord.notB (Nat.beq (wordMul mul RB (p ++ q) Y) Z) = true := by
  rw [wordMul_append, Nat.eq_of_beq_eq_true h1]
  exact h2

theorem beq_wordMul_of_eq {mul : Nat → Nat → Nat} {RB : Nat → Nat} {w w' : List Nat} {Y Z : Nat}
    (hw : w = w') (h : Nat.beq (wordMul mul RB w' Y) Z = true) :
    Nat.beq (wordMul mul RB w Y) Z = true :=
  hw ▸ h

theorem notB_beq_wordMul_of_eq {mul : Nat → Nat → Nat} {RB : Nat → Nat} {w w' : List Nat}
    {Y Z : Nat} (hw : w = w') (h : CFSG.KC.Ord.notB (Nat.beq (wordMul mul RB w' Y) Z) = true) :
    CFSG.KC.Ord.notB (Nat.beq (wordMul mul RB w Y) Z) = true :=
  hw ▸ h

end CFSG.KC.Fi24Fix

end
