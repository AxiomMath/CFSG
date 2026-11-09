module

public import Certificates.Kernel.Sporadic.RawGenSchOJ
public import CFSG.Certificates.Kernel.Spor.RawSchXSound
public meta import Certificates.Kernel.Sporadic.RawGenSchOJ
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KS.RawGenSchX

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchO

meta def subE (a b : Expr) : Expr :=
  mkAppN (mkConst ``HSub.hSub [0, 0, 0])
    #[natT, natT, natT, mkApp2 (mkConst ``instHSub [0]) natT (mkConst ``instSubNat), a, b]

meta def schXT (c : Ctx) (CH : Nat) (nDE iE TE sE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schKX)
    #[c.nE, c.wE, c.mE, c.nwE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, lit c.kS, c.k `BP,
      lit c.nb, iE, TE, mulE sE (lit CH), lit CH,
      mkAppN (mkConst ``CFSG.KS.Raw.xPtsK) #[c.wE, c.mE, c.k `BP, lit c.nb, nDE],
      addE (lit c.nb) (subE c.nE nDE)])

meta def faithOf (P : Name) : CommandElabM (Option Expr) := do
  unless (← getEnv).contains (P ++ `faith) do return none
  return some (← getConstInfo (P ++ `faith)).type.getAppArgs[1]!

meta def addHlx (c : Ctx) : CommandElabM Unit := do
  let P := c.P
  if (← getEnv).contains (P ++ `hlx) then return
  let LCH ← natOf (P ++ `pLCH)
  let NL ← natOf (P ++ `NL)
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
      addThm (P ++ Name.mkSimple s!"lvx{i}") (lvT c iE) v
    let lvP := mkLambda `i .default natT (lvT c (mkBVar 0))
    let hlV := forallChain lvP c.nb fun i => mkConst (P ++ Name.mkSimple s!"lvx{i}")
    let hlT := mkAppN (mkConst ``CFSG.KS.Raw.LevelsOK)
      #[c.nE, c.wE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, lit c.kS, lit c.nb, c.k `BP]
    addThm (P ++ `hlx) hlT hlV

meta def ltE (i nb : Nat) : Expr :=
  mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (lit (i + 1)) (lit nb) rflT

end CFSG.KS.RawGenSchX

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchO CFSG.KS.RawGenSchX in
elab_rules : command
  | `(#ks_rawchain_sl2_sch $pre:ident $ii:num $lo:num $hi:num) => do
    let P := pre.getId
    let some nDE ← faithOf P | throwUnsupportedSyntax
    let c ← ctxOf P
    let CH ← natOf (P ++ `pCH)
    addHlx c
    let i := ii.getNat
    withSync do
      for s in [lo.getNat:hi.getNat] do
        let xN := P ++ Name.mkSimple s!"schx{i}_{s}"
        addRefl xN (schXT c CH nDE (lit i) (c.steps (lit i)) (lit s))
        let v := mkAppN (mkConst ``CFSG.KS.Raw.Orb.schK_of_schKX_steps)
          #[c.nE, nDE, c.wE, lit c.kS, lit c.nb, c.k `BP, lit i, mulE (lit s) (lit CH), lit CH,
            c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, mkConst (P ++ `faith),
            mkConst (P ++ `hlx), ltE i c.nb, mkConst xN]
        addThm (P ++ Name.mkSimple s!"sch{i}_{s}") (schT c CH (lit i) (lit s)) v

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchO CFSG.KS.RawGenSchX in
elab_rules : command
  | `(#ks_rawchain_sl2_scho $pre:ident $lo:num $hi:num) => do
    let P := pre.getId
    let some nDE ← faithOf P | throwUnsupportedSyntax
    let c ← ctxOf P
    let CH ← natOf (P ++ `pCH)
    let TS ← natOf (P ++ `pTS)
    addHlx c
    withSync do
      for s in [lo.getNat:hi.getNat] do
        let xN := P ++ Name.mkSimple s!"sox_{s}"
        addRefl xN (schXT c CH nDE (lit 0) (lit TS) (lit s))
        let v := mkAppN (mkConst ``CFSG.KS.Raw.Orb.schK_of_schKX_tsb)
          #[c.nE, nDE, c.wE, lit c.kS, lit c.nb, c.k `BP, lit 0, lit TS, mulE (lit s) (lit CH),
            lit CH, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, mkConst (P ++ `faith),
            mkConst (P ++ `hlx), ltE 0 c.nb, mkConst (P ++ `tsb), mkConst xN]
        addThm (P ++ Name.mkSimple s!"so_{s}") (soT c CH TS (lit s)) v

end
