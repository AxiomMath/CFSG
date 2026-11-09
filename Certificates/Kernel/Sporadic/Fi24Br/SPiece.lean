module

public import Certificates.Kernel.Sporadic.Fi24Br.Prog
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.BrFi24 MS "Certificates/Kernel/Sporadic/Fi24Br/data/ssplit.bin" 152491 5
  2744838 7275162362727104204

public section

namespace CFSG.KD.BrFi24

open CFSG.KC.Ord

@[expose] noncomputable def oneIs (T : Nat) : List Nat → Bool
  | [x] => Nat.beq x T
  | _ => false

theorem oneIs_eq {T : Nat} : ∀ {s : List Nat}, oneIs T s = true → s = [T]
  | [x], h => by rw [Nat.eq_of_beq_eq_true h]
  | [], h => absurd h Bool.false_ne_true
  | _ :: _ :: _, h => absurd h Bool.false_ne_true

theorem progVal_append (RB : Nat → Nat) (L : Nat) (RS : Nat → Nat) (mul : Nat → Nat → Nat)
    (ONE : Nat) (Q : List Nat) :
    ∀ (P st : List Nat), progVal RB L RS mul ONE (P ++ Q) st =
      progVal RB L RS mul ONE Q (progVal RB L RS mul ONE P st)
  | [], _ => rfl
  | _ :: P, st => progVal_append RB L RS mul ONE Q P _

theorem sC_of_pieces {k : Nat} {P0 P1 P2 : List Nat} {X0 X1 : Nat}
    (h0 : oneIs X0 (progVal RB 11 RS MUL ONE P0 []) = true)
    (h1 : oneIs X1 (progVal RB 11 RS MUL ONE P1 [X0]) = true)
    (h2 : oneIs (RS k) (progVal RB 11 RS MUL ONE P2 [X1]) = true)
    (e : PS k = P0 ++ P1 ++ P2) : sC k = true := by
  have hv : progVal RB 11 RS MUL ONE (PS k) [] = [RS k] := by
    rw [e, progVal_append, progVal_append, oneIs_eq h0, oneIs_eq h1, oneIs_eq h2]
  change Nat.beq (hdN ONE (progVal RB 11 RS MUL ONE (PS k) [])) (RS k) = true
  rw [hv]
  exact Nat.beq_refl _

end CFSG.KD.BrFi24

end
