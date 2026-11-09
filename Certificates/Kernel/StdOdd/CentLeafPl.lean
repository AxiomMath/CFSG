module

public import Certificates.Data.Kernel.StdOdd.Chain

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain

@[expose] noncomputable def leafPl (F : Nat → Nat) (w k : Nat) : List Nat :=
  forceNL (full w) fun M =>
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih c => List.cons (Nat.land (F c) M) (ih (Nat.succ c))) k 0

theorem lenN_leafPl (F : Nat → Nat) (w k : Nat) : lenN (leafPl F w k) = k := by
  suffices H : ∀ M j, lenN (Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
      (fun _ ih c => List.cons (Nat.land (F c) M) (ih (Nat.succ c))) k j) = k by
    unfold leafPl forceNL
    cases full w <;> exact H _ _
  intro M
  induction k with
  | zero => intro j; rfl
  | succ n ih => intro j; exact congrArg Nat.succ (ih _)

end CFSG.KD.StdOdd.Cent

end
