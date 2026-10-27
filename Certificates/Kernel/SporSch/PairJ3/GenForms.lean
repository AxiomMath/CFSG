module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.SporSch.PairJ3CertSound
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab

open Lean Elab Command Meta

public section

open CFSG.KC.Tab in
meta def le70Bind (P0 sN : Name) : CommandElabM Unit := do
  let P := P0 ++ Name.mkSimple sN.lastComponentAsString
  let env ← getEnv
  let s ← match (env.find? sN).bind ConstantInfo.value? with
    | some (.lit (.strVal s)) => pure s
    | _ => throwError "#kss_le70: {sN} is not a string literal"
  let charE : Expr := mkConst ``Char
  let mk (ch : Char) : Expr := mkApp (mkConst ``Char.ofNat) (mkRawNatLit ch.toNat)
  let lst := s.toList.foldr (fun ch acc => mkApp3 (mkConst ``List.cons [0]) charE (mk ch) acc)
    (mkApp (mkConst ``List.nil [0]) charE)
  let lty := mkApp (mkConst ``List [0]) charE
  let strE := mkConst ``String
  let boolE := mkConst ``Bool
  let chE := mkConst (P ++ `chars)
  let eqT := mkApp3 (mkConst ``Eq [1]) strE (mkConst sN) (mkApp (mkConst ``String.ofList) chE)
  let leE := fun (cs : Expr) => mkApp (mkConst ``CFSG.KS.SporSch.le70K) cs
  let leT := mkApp3 (mkConst ``Eq [1]) boolE (leE chE) (mkConst ``Bool.true)
  let pred := mkLambda `cs .default lty (mkApp2 (mkConst ``And)
    (mkApp3 (mkConst ``Eq [1]) strE (mkConst sN) (mkApp (mkConst ``String.ofList) (mkBVar 0)))
    (mkApp3 (mkConst ``Eq [1]) boolE (leE (mkBVar 0)) (mkConst ``Bool.true)))
  let eqPf := mkApp2 (mkConst ``Eq.refl [1]) strE (mkConst sN)
  let okT := mkApp (mkConst ``CFSG.KS.SporSch.Le70Str) (mkConst sN)
  let okPf := mkAppN (mkConst ``Exists.intro [1]) #[lty, pred, chE,
    mkAppN (mkConst ``And.intro) #[eqT, leT, mkConst (P ++ `eq), mkConst (P ++ `le70)]]
  let thm := fun (nm : Name) (ty pf : Expr) =>
    ({ name := P ++ nm, levelParams := [], type := ty, value := pf } : TheoremVal)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `chars) lty lst
    CFSG.KC.addThmDecl (thm `eq eqT eqPf)
    CFSG.KC.addThmDecl (thm `le70 leT reflBoolTrue)
    CFSG.KC.addThmDecl (thm `ok okT okPf)

elab "#kss_le70 " pre:ident ss:ident+ : command => do
  for sId in ss do
    le70Bind pre.getId (← liftCoreM <| realizeGlobalConstNoOverload sId)

meta partial def le70Proof (P : Name) (e : Expr) : MetaM Expr := do
  if e.isAppOfArity ``HAppend.hAppend 6 then
    let a := e.getArg! 4
    let b := e.getArg! 5
    return mkAppN (mkConst ``CFSG.KS.SporSch.Le70Str.append) #[a, b, ← le70Proof P a,
      ← le70Proof P b]
  let some c := e.constName? | throwError "le70_concat: unexpected term {e}"
  let nm := P ++ Name.mkSimple c.lastComponentAsString ++ `ok
  if (← getEnv).contains nm then return mkConst nm
  let some (.defnInfo d) := (← getEnv).find? c
    | throwError "le70_concat: no theorem {nm} and no definition of {c}"
  le70Proof P d.value

elab "le70_concat " pre:ident : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let ty ← instantiateMVars (← g.getType)
    let some s := ty.app1? ``CFSG.KS.SporSch.Le70Str
      | throwError "le70_concat: the goal is not `Le70Str _`"
    g.assign (← le70Proof pre.getId s)

end
