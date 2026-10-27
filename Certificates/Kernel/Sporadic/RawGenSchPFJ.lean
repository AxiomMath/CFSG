module

public import Certificates.Kernel.Sporadic.RawGenSchPF
public import CFSG.Certificates.Kernel.Spor.RawSchPSound
public import CFSG.Certificates.Kernel.Spor.RawSchFSound
public meta import Certificates.Kernel.Sporadic.RawGenSchPF
public meta import Certificates.Kernel.Sporadic.RawGenSchP
public meta import Certificates.Kernel.Sporadic.RawGenSplit
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KS.RawGenSchPFJ

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchPF

meta def schFT (c : Ctx) (CH : Nat) (iE sE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schK)
    #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, lit c.kS,
      c.k `BP, lit c.nb, iE, fwE c iE, mulE sE (lit CH), lit CH])

meta def rflT : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

end CFSG.KS.RawGenSchPFJ

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchP CFSG.KS.RawGenSchPF
  CFSG.KS.RawGenSchPFJ in
elab "#ks_rawchain_sl2_joinpf " pre:ident fl:num : command => do
  let P := pre.getId
  let F := fl.getNat
  let c ← ctxOf P
  let LCH ← natOf (P ++ `pLCH)
  let CH ← natOf (P ++ `pCH)
  let NL ← natOf (P ++ `NL)
  let NS ← natOf (P ++ `NS)
  let mut nsi : Array Nat := #[]
  for i in [0:c.nb] do
    nsi := nsi.push (← natOf (P ++ Name.mkSimple s!"NS{i}"))
  let hdT := (← getConstInfo (P ++ `head)).type
  let hdA := hdT.getAppArgs[1]!.getAppArgs
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
      let nm := P ++ Name.mkSimple s!"lv{i}"
      addThm nm (lvT c iE) v
    let lvP := mkLambda `i .default natT (lvT c (mkBVar 0))
    let hlV := forallChain lvP c.nb fun i => mkConst (P ++ Name.mkSimple s!"lv{i}")
    let hlT := mkAppN (mkConst ``CFSG.KS.Raw.LevelsOK)
      #[c.nE, c.wE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, lit c.kS, lit c.nb, c.k `BP]
    addThm (P ++ `hl) hlT hlV
    if CH != 0 then
      let innerP := fun (iE : Expr) => mkLambda `s .default natT (schFT c CH iE (mkBVar 0))
      let outerBody := fun (iE : Expr) => forallLt (lit NS) fun sE =>
        schFT c CH (iE.liftLooseBVars 0 2) sE
      let outerP := mkLambda `i .default natT (outerBody (mkBVar 0))
      let hfV := forallChain outerP c.nb fun i =>
        let iE := lit i
        let hc := mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true)
            (mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (c.k `LR) iE)) (mulE (lit nsi[i]!) (lit CH)))
          rflT
        let inner := forallChain (innerP iE) nsi[i]! fun s =>
          if (F >>> i) % 2 == 1 then
            mkAppN (mkConst ``CFSG.KS.Raw.schK_of_schK2)
              #[c.nE, c.wE, lit c.kS, c.k `BP, lit c.nb, iE, fwE c iE, mulE (lit s) (lit CH),
                lit CH, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, mkConst (P ++ `hl),
                ltPf i c.nb, mkConst (P ++ Name.mkSimple s!"sf{i}_{s}")]
          else
            mkAppN (mkConst ``CFSG.KS.Raw.Orb.schK_fwdT_of_schK)
              #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI,
                lit c.kS, c.k `BP, lit c.nb, iE, c.steps iE, mulE (lit s) (lit CH), lit CH,
                mkAppN (mkConst ``CFSG.KS.Raw.schK_of_schK2)
                  #[c.nE, c.wE, lit c.kS, c.k `BP, lit c.nb, iE, c.steps iE,
                    mulE (lit s) (lit CH), lit CH, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI,
                    mkConst (P ++ `hl), ltPf i c.nb,
                    mkConst (P ++ Name.mkSimple s!"sq{i}_{s}")]]
        mkAppN (mkConst ``CFSG.KS.Raw.schK_slices)
          #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI,
            lit c.kS, c.k `BP, lit c.nb, iE, fwE c iE, lit NS, lit nsi[i]!, lit CH, hc, inner]
      let hNS := mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true) c.nE (mulE (lit NS) (lit CH)))
        rflT
      let hsV := mkAppN (mkConst ``CFSG.KS.Raw.schK_of_fwd)
        #[c.nE, c.wE, lit c.kS, kOE, lit c.nb, c.k `BP, lit NS, lit CH, c.k `S, c.k `SI,
          c.k `LR, c.k `TR, c.k `TRI, dE, mkConst (P ++ `head), mkConst (P ++ `hl), hNS, hfV]
      let hsT := forallLt (lit c.nb) fun iE => forallLt (lit NS) fun sE =>
        schT c CH (iE.liftLooseBVars 0 2) sE
      addThm (P ++ `hs) hsT hsV

end
