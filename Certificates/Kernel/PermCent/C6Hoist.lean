module

public import Certificates.Data.Kernel.PermCent.SmallF3TwinBase

public section

namespace CFSG.Certificates.Kernel.PkCV.SmallF3T

theorem all_cond_filter {α : Type} (L : List α) (c d r : α → Bool) :
    (L.all fun τ => bif c τ && d τ then r τ else true) =
      ((L.filter c).all fun τ => bif d τ then r τ else true) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.all_cons, List.filter_cons, ih]
    cases c a <;> rfl

theorem filter_and_filter {α : Type} (L : List α) (a b : α → Bool) :
    (L.filter fun u => a u && b u) = (L.filter a).filter b := by
  rw [List.filter_filter]
  congr 1
  funext u
  rw [Bool.and_comm]

section

variable {β : Type} (one : β) [DecidableEq β]

@[expose] def c6Gen (p2 p3 : β → Bool) (cm : β → β → Bool) (LA LP : List β) : Bool :=
  let LI := LA.filter fun τ => p2 τ
  (LP.filter fun y => p2 y && !decide (y = one)).all fun y =>
    (LP.filter fun u => p3 u && !decide (u = one) && cm y u).all fun u =>
      LI.all fun τ =>
        bif cm τ y && cm τ u then decide (τ = one) || decide (τ = y) else true

@[expose] def c6Hoist (p2 p3 : β → Bool) (cm : β → β → Bool) (LA LP : List β) : Bool :=
  let LI := LA.filter fun τ => p2 τ
  let L3 := LP.filter fun u => p3 u && !decide (u = one)
  (LP.filter fun y => p2 y && !decide (y = one)).all fun y =>
    let CY := LI.filter fun τ => cm τ y
    (L3.filter fun u => cm y u).all fun u =>
      CY.all fun τ => bif cm τ u then decide (τ = one) || decide (τ = y) else true

theorem c6Gen_eq (p2 p3 : β → Bool) (cm : β → β → Bool) (LA LP : List β) :
    c6Gen one p2 p3 cm LA LP = c6Hoist one p2 p3 cm LA LP := by
  unfold c6Gen c6Hoist
  simp only [filter_and_filter, all_cond_filter]

end

theorem c6freeC_eq {n : Nat} [Small n] (LA LP : List (CV n)) :
    c6freeC LA LP = c6Hoist (1 : CV n) (fun τ => powOneC τ 2) (fun u => powOneC u 3)
      (fun a b => eq22C a b b a) LA LP :=
  c6Gen_eq (1 : CV n) _ _ _ LA LP

end CFSG.Certificates.Kernel.PkCV.SmallF3T

end
