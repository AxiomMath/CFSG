module

public meta import Lean
public import Lean.Expr

public section

open Lean Meta Simp

simproc_decl strToList (String.toList _) := fun e => do
  unless e.isAppOfArity ``String.toList 1 do return .continue
  let a := e.appArg!
  let .lit (.strVal s) := a | return .continue
  let csE := toExpr s.toList
  let ofl := mkApp (mkConst ``String.ofList) csE
  let h1 ← mkExpectedTypeHint (← mkEqRefl a) (← mkEq a ofl)
  let h2 := mkApp (mkConst ``String.toList_ofList) csE
  let pf ← mkEqTrans (← Meta.mkCongrArg (mkConst ``String.toList) h1) h2
  return .done { expr := csE, proof? := pf }

end
