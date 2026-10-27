module

public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Kernel.StdOdd.SlpCmd
public import Lean.Exception

public section

namespace CFSG.KC.Misc.E6Std

open Lean Elab Command CFSG.KC.Tab

elab "#kc_vals " pre:ident fId:ident n:num : command => do
  let P := (← getCurrNamespace) ++ pre.getId
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let n := n.getNat
  let env ← getEnv
  let mut vals : Array Nat := #[]
  for k in [0:n] do
    match Kernel.whnf env {} (mkApp (mkConst fN) (lit k)) with
    | .ok e =>
      match e.rawNatLit? with
      | some v => vals := vals.push v
      | none => throwError "#kc_vals: {fN} {k} has no literal normal form"
    | .error _ => throwError "#kc_vals: kernel error at {fN} {k}"
  let lnT := mkApp (mkConst ``List [0]) natT
  let e := vals.toList.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc)
    (mkApp (mkConst ``List.nil [0]) natT)
  let VE := mkConst (P ++ `V)
  let stmt (k : Expr) : Expr :=
    mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp2 (mkConst ``Nat.beq) (mkApp (mkConst fN) k) (mkApp2 (mkConst ``nthV) VE k))
      (mkConst ``Bool.true)
  let motive := mkLambda `k .default natT (stmt (mkBVar 0))
  withSync do
    addDef (P ++ `V) lnT e
    let mut pf := mkApp (mkConst ``forall_lt_zero) motive
    for k in [0:n] do
      let nm := P ++ Name.mkSimple s!"e{k}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := stmt (lit k), value := reflBoolTrue }
      pf := mkApp4 (mkConst ``forall_lt_succ) motive (lit k) pf (mkConst nm)
    let lt (x y : Expr) : Expr := mkApp4 (mkConst ``LT.lt [0]) natT (mkConst ``instLTNat) x y
    let ty := mkForall `k .default natT (mkForall `h .default (lt (mkBVar 0) (lit n))
      (stmt (mkBVar 1)))
    CFSG.KC.addThmDecl <| { name := P ++ `all, levelParams := [], type := ty, value := pf }

end CFSG.KC.Misc.E6Std

end
