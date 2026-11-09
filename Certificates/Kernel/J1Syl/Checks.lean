module

public import Certificates.Kernel.J1Syl.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ1Syl

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.Sporadic.J1.Sylow.Native CertificateChecks.KernelSpor.J1K

theorem shape_ok : shapeOK = true := by decide +kernel
theorem keysOK_ok : keysOK = true := by quickRfl
theorem vKeys_ok : vKeysOK = true := by quickRfl
theorem fNe_ok : fNe = true := by quickRfl

@[expose] noncomputable def movesL (g gi : Nat → Nat) (l : List (List Int)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => bAnd(movesAll.notK (movesAll.memB
      (keyOf (g (xp w (gi (nat_lit 0)))) (g (xp w (gi (nat_lit 1))))) (keys2 w)), ih)) l

theorem movesAll_eq (g gi : Nat → Nat) : movesAll g gi = movesL g gi TWL.tail := rfl

theorem bAnd_eq' (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem movesL_append (g gi : Nat → Nat) :
    ∀ l1 l2, movesL g gi (l1 ++ l2) = (movesL g gi l1 && movesL g gi l2)
  | [], _ => rfl
  | w :: l1, l2 => by
    show bAnd(_, movesL g gi (l1 ++ l2)) = (bAnd(_, movesL g gi l1) && movesL g gi l2)
    rw [movesL_append g gi l1 l2, bAnd_eq', bAnd_eq', Bool.and_assoc]

theorem movesL_split (g gi : Nat → Nat) (l : List (List Int)) (b : Nat) :
    movesL g gi l = (movesL g gi (l.take b) && movesL g gi (l.drop b)) := by
  rw [← movesL_append, List.take_append_drop]

theorem b_ok0 : movesL (r32 BE) (fun x => r32 BE (r32 BE x)) (TWL.tail.take 732) = true := by
  quickRfl

theorem b_ok1 :
    movesL (r32 BE) (fun x => r32 BE (r32 BE x)) ((TWL.tail.drop 732).take 732) = true := by
  quickRfl

theorem b_ok2 :
    movesL (r32 BE) (fun x => r32 BE (r32 BE x)) (((TWL.tail.drop 732).drop 732).take 732) =
    true := by
  quickRfl

theorem b_ok3 :
    movesL (r32 BE) (fun x => r32 BE (r32 BE x)) (((TWL.tail.drop 732).drop 732).drop 732) =
    true := by
  quickRfl

theorem b_ok : bOK = true := by
  unfold bOK
  rw [movesAll_eq, movesL_split _ _ _ 732, movesL_split _ _ (TWL.tail.drop 732) 732,
    movesL_split _ _ ((TWL.tail.drop 732).drop 732) 732, b_ok0, b_ok1, b_ok2, b_ok3]
  rfl

end CertificateChecks.KernelJ1Syl

end
