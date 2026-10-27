module

public import Certificates.Kernel.Sporadic.RawGenSchO
public import CFSG.Certificates.Kernel.Spor.RawSch4OSound
public import CFSG.Certificates.Kernel.Spor.RawSchOSound
public meta import Certificates.Kernel.Sporadic.RawGenSchO
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchO in
elab "#ks_rawchain_sl2_joino " pre:ident : command => do
  let P := pre.getId
  let c ← ctxOf P
  unless 3 ≤ c.nb do throwError "#ks_rawchain_sl2_joino: {c.nb} levels, expected at least 3"
  let LCH ← natOf (P ++ `pLCH)
  let CH ← natOf (P ++ `pCH)
  let NL ← natOf (P ++ `NL)
  let NS ← natOf (P ++ `NS)
  let TS ← natOf (P ++ `pTS)
  let kO ← kOOf P
  let mut nsi : Array Nat := #[]
  for i in [0:c.nb] do
    nsi := nsi.push (← natOf (P ++ Name.mkSimple s!"NS{i}"))
  let hdA := (← getConstInfo (P ++ `head)).type.getAppArgs[1]!.getAppArgs
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
    let soP := mkLambda `s .default natT (soT c CH TS (mkBVar 0))
    let faV := forallChain soP nsi[0]! fun s => mkConst (P ++ Name.mkSimple s!"so_{s}")
    let faT := forallLt (lit nsi[0]!) fun sE => soT c CH TS sE
    addThm (P ++ `ofall) faT faV
    let innerP := fun (iE : Expr) => mkLambda `s .default natT (schT c CH iE (mkBVar 0))
    let chainAt := fun (i : Nat) =>
      forallChain (innerP (lit i)) nsi[i]! fun s => mkConst (P ++ Name.mkSimple s!"sch{i}_{s}")
    let subset := (← getEnv).contains (P ++ `pTJ)
    if c.nb == 4 && !subset then
      for s in [0:nsi[0]!] do
        let v := mkAppN (mkConst ``CFSG.KS.Raw.Orb.schK_of_sch4OL)
          #[c.nE, c.wE, lit c.kS, lit kO, c.k `BP, lit 0, lit TS, lit nsi[0]!, lit nsi[1]!,
            lit nsi[2]!, lit nsi[3]!, lit CH, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, dE,
            mkConst (P ++ `head), mkConst (P ++ `hl), mkConst (P ++ `inv), mkConst (P ++ `g12),
            mkConst (P ++ `g23), mkConst (P ++ `tsb), mkConst (P ++ `tso), hcE 0,
            mkConst (P ++ `ofall), hcE 1, chainAt 1, hcE 2, chainAt 2, hcE 3, chainAt 3,
            mulE (lit s) (lit CH), lit CH]
        addThm (P ++ Name.mkSimple s!"sch0_{s}") (schT c CH (lit 0) (lit s)) v
    else
      let lvP := mkLambda `k .default natT (lv12T c (addE (lit 0) (mkBVar 0)))
      let hlvV := forallChain lvP (c.nb - 2) fun k => mkConst (P ++ Name.mkSimple s!"g{k + 1}{k + 2}")
      let exBody := fun (lE NE : Expr) =>
        mkApp2 (mkConst ``And)
          (mkAppN (mkConst ``LE.le [0]) #[natT, mkConst ``instLENat,
            mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (c.k `LR) lE), mulE NE (lit CH)])
          (forallLt (NE.liftLooseBVars 0 1) fun sE => schT c CH (lE.liftLooseBVars 0 2) sE)
      let exT := fun (lE : Expr) => mkApp2 (mkConst ``Exists [1]) natT
        (mkLambda `N .default natT (exBody (lE.liftLooseBVars 0 1) (mkBVar 0)))
      let slP := mkLambda `k .default natT (exT (addE (addE (lit 0) (lit 1)) (mkBVar 0)))
      let hslV := forallChain slP (c.nb - 1) fun k =>
        let l := k + 1
        mkAppN (mkConst ``Exists.intro [1])
          #[natT, mkLambda `N .default natT (exBody (lit l) (mkBVar 0)), lit nsi[l]!,
            mkApp4 (mkConst ``And.intro) (exBody (lit l) (lit nsi[l]!)).appFn!.appArg!
              (exBody (lit l) (lit nsi[l]!)).appArg! (hcE l) (chainAt l)]
      let hE := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (lit 3) (lit c.nb) rflT
      for s in [0:nsi[0]!] do
        let common := #[c.nE, c.wE, lit c.kS, lit kO, c.k `BP, lit c.nb, lit 0, lit TS]
        let v :=
          if subset then
            mkAppN (mkConst ``CFSG.KS.Raw.Orb.schK_of_schOL_wds)
              (common ++ #[mkConst (P ++ `pTJ), lit nsi[0]!, lit CH, c.k `S, c.k `SI, c.k `LR,
                c.k `TR, c.k `TRI, dE, mkConst (P ++ `oWS), mkConst (P ++ `head), mkConst (P ++ `hl),
                hE, mkConst (P ++ `inv), hlvV, mkConst (P ++ `tsb), mkConst (P ++ `owd),
                mkConst (P ++ `oinc), hcE 0, mkConst (P ++ `ofall), hslV, mulE (lit s) (lit CH),
                lit CH])
          else
            mkAppN (mkConst ``CFSG.KS.Raw.Orb.schK_of_schOL_orig)
              (common ++ #[lit nsi[0]!, lit CH, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, dE,
                mkConst (P ++ `head), mkConst (P ++ `hl), hE, mkConst (P ++ `inv), hlvV,
                mkConst (P ++ `tsb), mkConst (P ++ `tso), hcE 0, mkConst (P ++ `ofall), hslV,
                mulE (lit s) (lit CH), lit CH])
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
