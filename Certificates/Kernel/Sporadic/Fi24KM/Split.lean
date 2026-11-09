module

public import Certificates.Kernel.Sporadic.Fi24KM.Prog

public section

namespace CFSG.KD.KMFi24

open CFSG.KC.Ord

@[expose] noncomputable def oneOK (st : List Nat) (v : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x t _ => Bool.rec (motive := fun _ => Bool) false
      (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) t) (Nat.beq x v)) st

theorem oneOK_spec {st : List Nat} {v : Nat} (h : oneOK st v = true) : st = [v] := by
  match st, h with
  | [], h => exact absurd h (by simp [oneOK])
  | x :: [], h =>
    have hb : Nat.beq x v = true := by
      revert h
      cases hb : Nat.beq x v
      · intro h; simp [oneOK, hb] at h
      · intro _; rfl
    rw [Nat.eq_of_beq_eq_true hb]
  | x :: y :: t, h =>
    exfalso
    revert h
    cases hb : Nat.beq x v <;> simp [oneOK, hb]

theorem progVal_append (RB : Nat → Nat) (L : Nat) (RS : Nat → Nat) (mul : Nat → Nat → Nat)
    (ONE : Nat) (P Q : List Nat) :
    ∀ st, progVal RB L RS mul ONE (P ++ Q) st = progVal RB L RS mul ONE Q (progVal RB L RS mul ONE P st) := by
  induction P with
  | nil => intro st; rfl
  | cons ins P ih => intro st; exact ih _

theorem progOK_split {RB : Nat → Nat} {L : Nat} {RS : Nat → Nat} {mul : Nat → Nat → Nat} {ONE : Nat}
    {P : List Nat} (P1 P2 : List Nat) {T v : Nat} (hP : P = P1 ++ P2)
    (h1 : oneOK (progVal RB L RS mul ONE P1 []) v = true)
    (h2 : Nat.beq (hdN ONE (progVal RB L RS mul ONE P2 [v])) T = true) :
    progOK RB L RS mul ONE P T = true := by
  unfold progOK progTop
  rw [hP, progVal_append, oneOK_spec h1]
  exact h2

end CFSG.KD.KMFi24

end
