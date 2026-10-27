module

public import Certificates.Kernel.Sporadic.RawGenSchPFJ
public import Certificates.Data.Kernel.Spor.RawSchU
public import Certificates.Data.Kernel.Spor.RawSch3F
public import CFSG.Certificates.Kernel.Spor.RawSchUSound
public meta import Certificates.Kernel.Sporadic.RawGenSchPFJ
public meta import Certificates.Kernel.Sporadic.RawGenSchPF
public meta import Certificates.Kernel.Sporadic.RawGenSchP
public meta import Certificates.Kernel.Sporadic.RawGenSplit
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KS.RawGenSchPU

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchPF

meta def unpackW (n w v : Nat) : Array Nat :=
  Array.ofFn (n := n) fun x => (v >>> (x.val * w)) % (1 <<< w)

meta def sch2uT (c : Ctx) (CH D : Nat) (iE sE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schK2U)
    #[c.nE, c.wE, c.mE, c.nwE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, c.k `U, lit c.kS,
      c.k `BP, lit D, lit c.nb, iE, fwE c iE, mulE sE (lit CH), lit CH])

end CFSG.KS.RawGenSchPU

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchPU in
elab "#ks_rawchain_sl2_utab " pre:ident sId:ident bId:ident : command => do
  let P := pre.getId
  let c ← ctxOf P
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let S ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) sN
  let base ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  if base.size != c.nb || S.size != c.kS || c.nb < 3 then
    throwError "#ks_rawchain_sl2_utab: the generators or base differ from the data of {P}"
  let (_, cnts, trs, _) := levels c.n c.w S base true
  let L := c.nb - 3
  let off1 := (cnts.extract 0 (L + 1)).foldl (· + ·) 0
  let off2 := off1 + cnts[L + 1]!
  let D := cnts[L + 2]!
  let mut us : Array Nat := #[]
  for a in [0:cnts[L + 1]!] do
    for b in [0:D] do
      us := us.push (pack c.w (comp c.n (unpackW c.n c.w trs[off1 + a]!)
        (unpackW c.n c.w trs[off2 + b]!)))
  withSync do
    addTree (P ++ `U) us
    addDef (P ++ `pD) natT (lit D)
    addRefl (P ++ `ut) (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.utabF)
      #[c.nE, c.wE, c.mE, c.nwE, c.k `LR, c.k `TR, c.k `U, lit L, lit D]))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchPU in
elab "#ks_rawchain_sl2_schpu " pre:ident ii:num lo:num hi:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let CH ← natOf (P ++ `pCH)
  let D ← natOf (P ++ `pD)
  withSync do
    for s in [lo.getNat:hi.getNat] do
      addRefl (P ++ Name.mkSimple s!"su{ii.getNat}_{s}") (sch2uT c CH D (lit ii.getNat) (lit s))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit CFSG.KS.RawGenSchP CFSG.KS.RawGenSchPF
  CFSG.KS.RawGenSchPFJ in
elab "#ks_rawchain_sl2_joinpfu " pre:ident fl:num gl:num : command => do
  let P := pre.getId
  let F := fl.getNat
  let G := gl.getNat
  let c ← ctxOf P
  let LCH ← natOf (P ++ `pLCH)
  let CH ← natOf (P ++ `pCH)
  let NL ← natOf (P ++ `NL)
  let NS ← natOf (P ++ `NS)
  let D ← if G != 0 then natOf (P ++ `pD) else pure 0
  if G &&& F != G || (G != 0 && c.nb < 3) || G >>> (c.nb - 2) != 0 then
    throwError "#ks_rawchain_sl2_joinpfu: bad level masks {F} {G}"
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
            let sfV := if (G >>> i) % 2 == 1 then
                mkAppN (mkConst ``CFSG.KS.Raw.schK2_of_schK2U)
                  #[c.nE, c.wE, lit c.kS, c.k `BP, lit D, lit (c.nb - 3), lit c.nb, iE, fwE c iE,
                    mulE (lit s) (lit CH), lit CH, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI,
                    c.k `U, mkConst (P ++ `hl), mkApp2 (mkConst ``Eq.refl [1]) natT (lit c.nb),
                    mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true) (lit (i + 3)) (lit c.nb)) rflT,
                    mkConst (P ++ `ut), mkConst (P ++ Name.mkSimple s!"su{i}_{s}")]
              else mkConst (P ++ Name.mkSimple s!"sf{i}_{s}")
            mkAppN (mkConst ``CFSG.KS.Raw.schK_of_schK2)
              #[c.nE, c.wE, lit c.kS, c.k `BP, lit c.nb, iE, fwE c iE, mulE (lit s) (lit CH),
                lit CH, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, mkConst (P ++ `hl),
                ltPf i c.nb, sfV]
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
