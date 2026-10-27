module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

public section

namespace CFSG.KC.J4Q

theorem forall_lt_zero' {P : Nat → Prop} : ∀ t < 0, P t := fun _ h => absurd h (Nat.not_lt_zero _)

theorem forall_lt_succ' {P : Nat → Prop} {n : Nat} (h : ∀ t < n, P t) (hn : P n) :
    ∀ t < Nat.succ n, P t := by
  intro t ht
  rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h1 | rfl
  · exact h t h1
  · exact hn

open Lean Elab Command

meta def addAll (P f : Name) (n : Nat) : CoreM Unit := do
  let boolT := mkConst ``Bool
  let natT := mkConst ``Nat
  let fk (k : Nat) : Expr := mkApp (mkConst f) (mkRawNatLit k)
  let isT (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolT e (mkConst ``Bool.true)
  for k in [0:n] do
    let name := P ++ Name.mkSimple s!"t{k}"
    let type := isT (fk k)
    let value := Lean.reflBoolTrue
    CFSG.KC.addThmDecl <| { name, levelParams := [], type, value }
  let pred := mkLambda `t .default natT (isT (mkApp (mkConst f) (mkBVar 0)))
  let mut pf := mkApp (mkConst ``forall_lt_zero') pred
  for k in [0:n] do
    pf := mkAppN (mkConst ``forall_lt_succ') #[pred, mkRawNatLit k, pf, mkConst (P ++ Name.mkSimple s!"t{k}")]
  let ty := mkForall `t .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, mkRawNatLit n])
    (isT (mkApp (mkConst f) (mkBVar 1))))
  let name := P ++ `all
  CFSG.KC.addThmDecl <| { name, levelParams := [], type := ty, value := pf }

elab "#j4q_all " P:ident f:ident n:num : command =>
  liftCoreM <| withOptions (Elab.async.set · false) do
    let f ← realizeGlobalConstNoOverload f
    addAll P.getId f n.getNat

end CFSG.KC.J4Q
