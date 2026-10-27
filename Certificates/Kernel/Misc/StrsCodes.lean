module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab
public import Lean.Exception

open Lean Elab Command Meta

meta def strsListLit (ty : Expr) (l : List Expr) : Expr :=
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc)
    (mkApp (mkConst ``List.nil [0]) ty)

open CFSG.KC.Tab in
elab "#ks_strs_codes " pre:ident t:term:max d:ident alpha:str : command => do
  let P := pre.getId
  let dN ← liftCoreM <| realizeGlobalConstNoOverload d
  let alpha := alpha.getString.toList
  let strE := mkConst ``String
  let charE := mkConst ``Char
  let lstrT := mkApp (mkConst ``List [0]) strE
  let (e, ss) ← liftTermElabM do
    let e ← Term.elabTermEnsuringType t lstrT
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ss ← unsafe evalExpr (List String) lstrT e
    return (e, ss)
  let mut words : Array Expr := #[]
  for s in ss do
    let mut cs : Array Expr := #[]
    for ch in s.toList do
      match alpha.idxOf? ch with
      | some i => cs := cs.push (lit i)
      | none => throwError "#ks_strs_codes: character {repr ch} is not in the alphabet"
    words := words.push (strsListLit natT cs.toList)
  let lnT := mkApp (mkConst ``List [0]) natT
  let codesE := strsListLit lnT words.toList
  let wFn := mkLambda `w .default lnT (mkApp (mkConst ``String.ofList)
    (mkApp4 (mkConst ``List.map [0, 0]) natT charE (mkConst dN) (mkBVar 0)))
  let rhs := mkApp4 (mkConst ``List.map [0, 0]) lnT strE wFn (mkConst (P ++ `codes))
  withSync do
    addDef (P ++ `codes) (mkApp (mkConst ``List [0]) lnT) codesE
    let ty := mkApp3 (mkConst ``Eq [1]) lstrT e rhs
    let pf := mkApp2 (mkConst ``Eq.refl [1]) lstrT e
    CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := ty, value := pf }
