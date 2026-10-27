module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.Tab
public import Lean.Exception

open Lean Elab Command

namespace CFSG.KS.HNRowTab

meta partial def natsOf (e : Expr) (acc : Array Nat) : Option (Array Nat) :=
  match e.getAppFnArgs with
  | (``List.cons, #[_, h, t]) =>
    match h.rawNatLit? with
    | some n => natsOf t (acc.push n)
    | none => none
  | (``List.nil, #[_]) => some acc
  | _ => none

end CFSG.KS.HNRowTab

elab "#hn_rowtab " f:ident l:ident : command => do
  let src ← liftCoreM <| realizeGlobalConstNoOverload l
  let some v := ((← getEnv).find? src).bind (·.value?)
    | throwError "#hn_rowtab: no value for {src}"
  let some vals := CFSG.KS.HNRowTab.natsOf v #[]
    | throwError "#hn_rowtab: {src} is not a literal list"
  let mut size := 1
  while size < vals.size do
    size := 2 * size
  let leaf := fun k => CFSG.KC.Tab.constFn (CFSG.KC.Tab.lit (vals.getD k 0))
  let ns ← getCurrNamespace
  CFSG.KC.Tab.withSync <|
    CFSG.KC.Tab.addDef (ns ++ f.getId) CFSG.KC.Tab.fnT (CFSG.KC.Tab.table leaf size 0)
