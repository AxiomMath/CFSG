module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Certificates.Kernel.Spor.RawSch3GSound
public meta import Certificates.Kernel.Sporadic.RawGenSplit
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KS.RawGenSchG

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit

meta def rflT : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

meta def sgT (c : Ctx) (CH D TJ : Nat) (sE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.sch3F)
    #[c.nE, c.wE, c.mE, c.nwE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, c.k `U, lit c.kS,
      c.k `BP, lit 0, lit TJ, lit D, mulE sE (lit CH), lit CH])

end CFSG.KS.RawGenSchG

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#ks_rawchain_sl2_gsub " pre:ident "(" js:num* ")" wId:ident : command => do
  let P := pre.getId
  let c ← ctxOf P
  unless c.nb == 3 do throwError "#ks_rawchain_sl2_gsub: {c.nb} levels, expected 3"
  let J := js.map (·.getNat)
  let wN ← liftCoreM <| realizeGlobalConstNoOverload wId
  let JJ := J ++ J
  let TJ := (List.range JJ.size).foldl (fun acc k => acc ||| (JJ[k]! <<< (8 + 8 * k))) JJ.size
  withSync do
    addDef (P ++ `pTJ) natT (lit TJ)
    addRefl (P ++ `inv) (isTrue (mkApp2 (mkConst ``CFSG.KS.Raw.invTabK) (lit c.kS) (c.steps (lit 0))))
    addRefl (P ++ `g12) (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lv12K)
      #[c.wE, c.mE, c.k `S, c.k `SI, lit c.kS, c.k `BP, lit 0, c.steps (lit 1), c.steps (lit 2)]))
    addRefl (P ++ `wd) (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.wdsK)
      #[c.nE, c.wE, c.mE, c.idE, c.k `S, c.k `SI, lit c.kS, lit TJ, mkConst wN, lit 0]))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchG in
elab "#ks_rawchain_sl2_schg " pre:ident lo:num hi:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let CH ← natOf (P ++ `pCH)
  let D ← natOf (P ++ `pD)
  let TJ ← natOf (P ++ `pTJ)
  withSync do
    for s in [lo.getNat:hi.getNat] do
      addRefl (P ++ Name.mkSimple s!"sg_{s}") (sgT c CH D TJ (lit s))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchG in
elab "#ks_rawchain_sl2_joing " pre:ident wId:ident : command => do
  let P := pre.getId
  let c ← ctxOf P
  unless c.nb == 3 do throwError "#ks_rawchain_sl2_joing: {c.nb} levels, expected 3"
  let wN ← liftCoreM <| realizeGlobalConstNoOverload wId
  let LCH ← natOf (P ++ `pLCH)
  let CH ← natOf (P ++ `pCH)
  let NL ← natOf (P ++ `NL)
  let NS ← natOf (P ++ `NS)
  let D ← natOf (P ++ `pD)
  let TJ ← natOf (P ++ `pTJ)
  let mut nsi : Array Nat := #[]
  for i in [0:c.nb] do
    nsi := nsi.push (← natOf (P ++ Name.mkSimple s!"NS{i}"))
  let hdA := (← getConstInfo (P ++ `head)).type.getAppArgs[1]!.getAppArgs
  let kOE := hdA[8]!
  let dE := hdA[9]!
  withSync do
    for i in [0:c.nb] do
      let iE := lit i
      let slP := mkLambda `s .default natT (lvSlT c LCH iE (mkBVar 0))
      let hsV := forallChain slP NL fun s => mkConst (P ++ Name.mkSimple s!"ls{i}_{s}")
      let hN := mkApp2 (mkConst ``Nat.le_of_ble_eq_true) c.nE (mulE (lit NL) (lit LCH))
      let v := mkAppN (mkConst ``CFSG.KS.Raw.levelK_of_sl)
        #[c.nE, c.wE, c.mE, c.nwE, c.pmE, c.idE, lit c.kS, c.root iE, c.steps iE,
          mkApp (c.k `LR) iE, lit NL, lit LCH, c.k `S, c.k `SI, c.k `TR, c.k `TRI,
          mkConst (P ++ Name.mkSimple s!"lh{i}"), hsV, mkApp hN rflT]
      addThm (P ++ Name.mkSimple s!"lv{i}") (lvT c iE) v
    let lvP := mkLambda `i .default natT (lvT c (mkBVar 0))
    let hlV := forallChain lvP c.nb fun i => mkConst (P ++ Name.mkSimple s!"lv{i}")
    let hlT := mkAppN (mkConst ``CFSG.KS.Raw.LevelsOK)
      #[c.nE, c.wE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, lit c.kS, lit c.nb, c.k `BP]
    addThm (P ++ `hl) hlT hlV
    let hcE := fun (i : Nat) => mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true)
        (mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (c.k `LR) (lit i))) (mulE (lit nsi[i]!) (lit CH)))
      rflT
    let sgP := mkLambda `s .default natT (sgT c CH D TJ (mkBVar 0))
    let faV := forallChain sgP nsi[0]! fun s => mkConst (P ++ Name.mkSimple s!"sg_{s}")
    let faT := forallLt (lit nsi[0]!) fun sE => sgT c CH D TJ sE
    addThm (P ++ `fall) faT faV
    let innerP := fun (iE : Expr) => mkLambda `s .default natT (schT c CH iE (mkBVar 0))
    let chainAt := fun (i : Nat) =>
      forallChain (innerP (lit i)) nsi[i]! fun s => mkConst (P ++ Name.mkSimple s!"sch{i}_{s}")
    for s in [0:nsi[0]!] do
      let v := mkAppN (mkConst ``CFSG.KS.Raw.Orb.schK_of_sch3GL)
        #[c.nE, c.wE, lit c.kS, kOE, c.k `BP, lit 0, lit D, lit nsi[0]!, lit nsi[1]!,
          lit nsi[2]!, lit CH, lit TJ, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, c.k `U, dE,
          mkConst wN, mkConst (P ++ `head), mkConst (P ++ `hl), mkConst (P ++ `inv),
          mkConst (P ++ `g12), mkConst (P ++ `ut), mkConst (P ++ `wd), hcE 0, mkConst (P ++ `fall),
          hcE 1, chainAt 1, hcE 2, chainAt 2, mulE (lit s) (lit CH), lit CH]
      addThm (P ++ Name.mkSimple s!"sch0_{s}") (schT c CH (lit 0) (lit s)) v
    let outerBody := fun (iE : Expr) => forallLt (lit NS) fun sE =>
      schT c CH (iE.liftLooseBVars 0 2) sE
    let outerP := mkLambda `i .default natT (outerBody (mkBVar 0))
    let hsV := forallChain outerP c.nb fun i =>
      let iE := lit i
      mkAppN (mkConst ``CFSG.KS.Raw.schK_slices)
        #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI,
          lit c.kS, c.k `BP, lit c.nb, iE, c.steps iE, lit NS, lit nsi[i]!, lit CH, hcE i,
          chainAt i]
    let hsT := forallLt (lit c.nb) fun iE => outerBody iE
    addThm (P ++ `hs) hsT hsV

end
