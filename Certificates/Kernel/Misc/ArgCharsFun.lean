module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command Meta

meta partial def funArgLeaves (t : Expr) : String :=
  match t.consumeMData with
  | .lit (.strVal s) => s
  | t' => match CFSG.KC.StrLits.appendArgs? t' with
    | some (a, b) => funArgLeaves a ++ funArgLeaves b
    | none => ""

open CFSG.KC.Tab in
elab "#kc_fun_arg_chars " pre:ident dId:ident : command => do
  let P := pre.getId
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let some info := (← getEnv).find? dN
    | throwError "#kc_fun_arg_chars: unknown constant `{dN}`"
  unless info.levelParams.isEmpty do
    throwError "#kc_fun_arg_chars: `{dN}` has universe parameters"
  let some body := info.value?
    | throwError "#kc_fun_arg_chars: `{dN}` has no visible definition"
  let lty := mkApp (mkConst ``List [0]) (mkConst ``Char)
  let strE := mkConst ``String
  let charsC := mkConst (P ++ `chars)
  let (ty, pf, leaves) ← liftTermElabM do
    lambdaTelescope body fun xs inner => do
      let inner := inner.consumeMData
      let fn := inner.getAppFn
      let args := inner.getAppArgs
      if args.isEmpty then throwError "#kc_fun_arg_chars: the body of `{dN}` is not an application"
      let t := args.back!
      if t.hasFVar then throwError "#kc_fun_arg_chars: the string argument depends on the binders"
      let pre := args.pop
      let (_, h) ← CFSG.KC.StrLits.build t none
      let g := mkLambda `s .default strE (mkAppN fn (pre.push (.bvar 0)))
      let pf ← mkCongrArg g (← mkEqSymm h)
      let ty ← mkEq (mkAppN (mkConst dN) xs)
        (mkAppN fn (pre.push (mkApp (mkConst ``String.ofList) charsC)))
      return (← mkForallFVars xs ty, ← mkLambdaFVars xs pf, funArgLeaves t)
  withSync do
    addDef (P ++ `chars) lty (CFSG.KC.StrLits.charsE leaves)
    CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := ty, value := pf }
