module

public import Certificates.Data.Kernel.CycTab

public section

namespace CFSG.KC.CycTab

@[expose] noncomputable def swapS (a b x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (swapK a b (nat_lit 0)) (fun k _ => swapK a b (Nat.succ k)) x

@[expose] noncomputable def cycGoS (n x : Nat) (a : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => x)
    (fun b _ ih a => swapS (Nat.mod a n) (Nat.mod b n) (ih b)) l a

@[expose] noncomputable def cycS (n : Nat) (c : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun a l _ => cycGoS n x a l) c

@[expose] noncomputable def cycsS (n : Nat) (cs : List (List Nat)) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun c _ ih => cycS n c ih) cs

theorem swapS_eq (a b x : Nat) : swapS a b x = swapK a b x := by
  cases x <;> rfl

theorem cycGoS_eq (n x : Nat) (a : Nat) (l : List Nat) : cycGoS n x a l = cycGoK n x a l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    change swapS (Nat.mod a n) (Nat.mod b n) (cycGoS n x b l) =
      swapK (Nat.mod a n) (Nat.mod b n) (cycGoK n x b l)
    rw [swapS_eq, ih]

theorem cycS_eq (n : Nat) (c : List Nat) (x : Nat) : cycS n c x = cycK n c x := by
  cases c with
  | nil => rfl
  | cons a l => exact cycGoS_eq n x a l

theorem cycsS_eq (n : Nat) (cs : List (List Nat)) : cycsS n cs = cycsK n cs := by
  funext x
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change cycS n c (cycsS n cs x) = cycK n c (cycsK n cs x)
    rw [cycS_eq, ih]

end CFSG.KC.CycTab

end
