module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command Meta

meta partial def arrLeaves (t : Expr) : String :=
  match t.consumeMData with
  | .lit (.strVal s) => s
  | t' => match CFSG.KC.StrLits.appendArgs? t' with
    | some (a, b) => arrLeaves a ++ arrLeaves b
    | none => ""

meta partial def listEntries (l : Expr) : MetaM (Array Expr) := do
  let l := l.consumeMData
  if l.isAppOfArity ``List.nil 1 then return #[]
  if l.isAppOfArity ``List.cons 3 then
    return #[l.getArg! 1] ++ (← listEntries (l.getArg! 2))
  throwError "#kc_arr_chars: expected a literal list, found{indentExpr l}"

meta def listProof (ts : Array Expr) : MetaM Expr := do
  let strE := mkConst ``String
  let consS := mkApp (mkConst ``List.cons [0]) strE
  let mut pf ← mkEqRefl (mkApp (mkConst ``List.nil [0]) strE)
  for t in ts.reverse do
    let (_, h) ← CFSG.KC.StrLits.build t none
    pf ← mkCongr (← mkCongrArg consS (← mkEqSymm h)) pf
  return pf

open CFSG.KC.Tab in
elab "#kc_arr_chars " pre:ident dId:ident : command => do
  let P := pre.getId
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let some info := (← getEnv).find? dN
    | throwError "#kc_arr_chars: unknown constant `{dN}`"
  unless info.levelParams.isEmpty do
    throwError "#kc_arr_chars: `{dN}` has universe parameters"
  let some body := info.value?
    | throwError "#kc_arr_chars: `{dN}` has no visible definition"
  let body := body.consumeMData
  let strE := mkConst ``String
  let lstr := mkApp (mkConst ``List [0]) (mkConst ``Char)
  let llty := mkApp (mkConst ``List [0]) lstr
  let (isArr, l) :=
    if body.isAppOfArity ``List.toArray 2 then (true, body.getArg! 1)
    else if body.isAppOfArity ``Array.mk 2 then (true, body.getArg! 1)
    else (false, body)
  let charsC := mkConst (P ++ `chars)
  let (ts, ty, pf) ← liftTermElabM do
    let ts ← listEntries (← zetaReduce l)
    let hl ← listProof ts
    let mapped := mkApp4 (mkConst ``List.map [0, 0]) lstr strE (mkConst ``String.ofList) charsC
    if isArr then
      let toArr := mkApp (mkConst ``List.toArray [0]) strE
      let pf ← mkCongrArg toArr hl
      return (ts, ← mkEq (mkConst dN) (mkApp toArr mapped), pf)
    else
      return (ts, ← mkEq (mkConst dN) mapped, hl)
  let charsV := ts.foldr (fun t acc => mkApp3 (mkConst ``List.cons [0]) lstr
    (CFSG.KC.StrLits.charsE (arrLeaves t)) acc) (mkApp (mkConst ``List.nil [0]) lstr)
  withSync do
    addDef (P ++ `chars) llty charsV
    CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := ty, value := pf }
