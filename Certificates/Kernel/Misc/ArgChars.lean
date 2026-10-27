module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command Meta

meta partial def argLeaves (t : Expr) : String :=
  match t.consumeMData with
  | .lit (.strVal s) => s
  | t' => match CFSG.KC.StrLits.appendArgs? t' with
    | some (a, b) => argLeaves a ++ argLeaves b
    | none => ""

open CFSG.KC.Tab in
elab "#kc_arg_chars " pre:ident dId:ident : command => do
  let P := pre.getId
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let some info := (← getEnv).find? dN
    | throwError "#kc_arg_chars: unknown constant `{dN}`"
  unless info.levelParams.isEmpty do
    throwError "#kc_arg_chars: `{dN}` has universe parameters"
  let some body := info.value?
    | throwError "#kc_arg_chars: `{dN}` has no visible definition"
  let body := body.consumeMData
  let fn := body.getAppFn
  let args := body.getAppArgs
  if args.isEmpty then throwError "#kc_arg_chars: the body of `{dN}` is not an application"
  let t := args.back!
  let pre := args.pop
  let lty := mkApp (mkConst ``List [0]) (mkConst ``Char)
  let strE := mkConst ``String
  let charsC := mkConst (P ++ `chars)
  let (ty, pf) ← liftTermElabM do
    let (L, h) ← CFSG.KC.StrLits.build t none
    let g := mkLambda `s .default strE (mkAppN fn (pre.push (.bvar 0)))
    let pf ← mkCongrArg g (← mkEqSymm h)
    let ty ← mkEq (mkConst dN) (mkAppN fn (pre.push (mkApp (mkConst ``String.ofList) charsC)))
    return (ty, pf)
  withSync do
    addDef (P ++ `chars) lty (CFSG.KC.StrLits.charsE (argLeaves t))
    CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := ty, value := pf }
