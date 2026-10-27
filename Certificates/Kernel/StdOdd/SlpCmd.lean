module

public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Data.Kernel.Misc.E6Std
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

public section

namespace CFSG.KC.Misc.E6Std

theorem forall_lt_zero (P : Nat → Prop) : ∀ t < 0, P t := fun _ h => absurd h (Nat.not_lt_zero _)

theorem forall_lt_succ (P : Nat → Prop) (n : Nat) (h : ∀ t < n, P t) (hn : P n) :
    ∀ t < n + 1, P t := by
  intro t ht
  rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
  · exact h t ht
  · exact hn

meta def mulBT (A B : Nat) : Nat := Id.run do
  let R := ((1 <<< 24336) - 1) / ((1 <<< 156) - 1)
  let F := (1 <<< 156) - 1
  let mut acc := 0
  for k in [0:156] do
    acc := acc ^^^ ((((A >>> k) &&& R) * F) &&& (((B >>> (156 * k)) &&& F) * R))
  return acc

meta def oneBT (_ : Unit := ()) : Nat := ((1 <<< 24492) - 1) / ((1 <<< 157) - 1)

meta def runT (gens : Array Nat) (prog : List (List Nat)) : Array Nat :=
  prog.foldl (fun vals line => vals.push (line.foldl (fun acc i => mulBT acc vals[i]!) (oneBT ())))
    gens

open Lean Elab Command CFSG.KC.Tab

elab "#e6_slp " pre:ident progId:ident valsId:ident a:num b:num : command => do
  let P := (← getCurrNamespace) ++ pre.getId
  let progN ← liftCoreM <| realizeGlobalConstNoOverload progId
  let valsN ← liftCoreM <| realizeGlobalConstNoOverload valsId
  let prog ← liftTermElabM <| unsafe evalConst (List (List Nat)) progN
  let vals ← liftTermElabM <| unsafe evalConst (List Nat) valsN
  let V := runT #[vals.getD a.getNat 0, vals.getD b.getNat 0] prog
  let lnT := mkApp (mkConst ``List [0]) natT
  let e := V.toList.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc)
    (mkApp (mkConst ``List.nil [0]) natT)
  let progE := mkConst progN
  let VE := mkConst (P ++ `V)
  let line (t : Expr) : Expr :=
    mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp4 (mkConst ``slpLine) VE progE (lit 2) t) (mkConst ``Bool.true)
  let motive := mkLambda `t .default natT (line (mkBVar 0))
  withSync do
    addDef (P ++ `V) lnT e
    let mut pf := mkApp (mkConst ``forall_lt_zero) motive
    for t in [0:prog.length] do
      let nm := P ++ Name.mkSimple s!"l{t}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := line (lit t), value := reflBoolTrue }
      pf := mkApp4 (mkConst ``forall_lt_succ) motive (lit t) pf (mkConst nm)
    let lt (x y : Expr) : Expr := mkApp4 (mkConst ``LT.lt [0]) natT (mkConst ``instLTNat) x y
    let ty := mkForall `t .default natT (mkForall `h .default
      (lt (mkBVar 0) (mkApp (mkConst ``lenLL) progE)) (line (mkBVar 1)))
    CFSG.KC.addThmDecl <| { name := P ++ `lines, levelParams := [], type := ty, value := pf }

end CFSG.KC.Misc.E6Std

end
