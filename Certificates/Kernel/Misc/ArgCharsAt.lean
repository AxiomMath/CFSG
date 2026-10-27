module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command Meta

meta partial def argLeavesAt (t : Expr) : String :=
  match t.consumeMData with
  | .lit (.strVal s) => s
  | t' => match CFSG.KC.StrLits.appendArgs? t' with
    | some (a, b) => argLeavesAt a ++ argLeavesAt b
    | none => ""

open CFSG.KC.Tab in
elab "#kc_arg_chars_at " pre:ident dId:ident k:num : command => do
  let P := pre.getId
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let some info := (← getEnv).find? dN
    | throwError "#kc_arg_chars_at: unknown constant `{dN}`"
  unless info.levelParams.isEmpty do
    throwError "#kc_arg_chars_at: `{dN}` has universe parameters"
  let some body := info.value?
    | throwError "#kc_arg_chars_at: `{dN}` has no visible definition"
  let body := body.consumeMData
  let fn := body.getAppFn
  let args := body.getAppArgs
  let k := k.getNat
  unless k < args.size do
    throwError "#kc_arg_chars_at: the body of `{dN}` has {args.size} arguments"
  let a := args[k]!.consumeMData
  let gfn := a.getAppFn
  let gargs := a.getAppArgs
  if gargs.isEmpty then throwError "#kc_arg_chars_at: argument {k} of `{dN}` is not an application"
  let t := gargs.back!
  let gpre := gargs.pop
  let lty := mkApp (mkConst ``List [0]) (mkConst ``Char)
  let strE := mkConst ``String
  let charsC := mkConst (P ++ `chars)
  let mk (s : Expr) : Expr := mkAppN fn (args.set! k (mkAppN gfn (gpre.push s)))
  let (ty, pf) ← liftTermElabM do
    let (_, h) ← CFSG.KC.StrLits.build t none
    let g := mkLambda `s .default strE (mk (.bvar 0))
    let pf ← mkCongrArg g (← mkEqSymm h)
    let ty ← mkEq (mkConst dN) (mk (mkApp (mkConst ``String.ofList) charsC))
    return (ty, pf)
  withSync do
    addDef (P ++ `chars) lty (CFSG.KC.StrLits.charsE (argLeavesAt t))
    CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := ty, value := pf }
