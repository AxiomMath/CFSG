module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.SchTriv
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Mathlib.GroupTheory.Schreier

open Lean Elab Command

public section

namespace CFSG.KS.RawGenSplit

open CFSG.KC.Tab CFSG.KS.RawGen

meta def natOf (nm : Name) : CommandElabM Nat := do
  match (← getEnv).find? nm with
  | some ci => match ci.value? with
    | some (.lit (.natVal k)) => pure k
    | _ => throwError "{nm} is not a literal definition"
  | none => throwError "unknown constant {nm}"

meta def levels (n w : Nat) (S : Array (Array Nat)) (base : Array Nat) (withTr : Bool) :
    Array Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let kS := S.size
  let nb := base.size
  let Sinv := S.map (inv n)
  let mut recs : Array Nat := #[]
  let mut cnts : Array Nat := #[]
  let mut trs : Array Nat := #[]
  let mut tris : Array Nat := #[]
  let nw := n * w
  for i in [0:nb] do
    let idx := (List.range kS).filter fun j =>
      (List.range i).all fun t => (S[j]!)[base[t]!]! == base[t]!
    let steps := (idx.map fun j => S[j]!).toArray ++ (idx.map fun j => Sinv[j]!).toArray
    let root := base[i]!
    let mut pos : Array Nat := (Array.replicate n n).set! root 0
    let mut pts : Array Nat := #[root]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    let mut tr : Array (Array Nat) := if withTr then #[Array.range n] else #[]
    for h in [0:n] do
      if h < pts.size then
        let x := pts[h]!
        for j in [0:steps.size] do
          let s := steps[j]!
          let y := s[x]!
          if pos[y]! == n then
            pos := pos.set! y pts.size
            pts := pts.push y
            par := par.push h
            lab := lab.push j
            if withTr then tr := tr.push (comp n s tr[h]!)
    let off := trs.size
    let c := pts.size
    let pad := fun (a : Array Nat) => a ++ Array.replicate (n - a.size) 0
    let mut R := c
    R := R ||| (pack w (pad pts) <<< 16)
    R := R ||| (pack w pos <<< (16 + nw))
    R := R ||| (pack w (pad par) <<< (16 + 2 * nw))
    R := R ||| (pack 8 (pad lab) <<< (16 + 3 * nw))
    if withTr then R := R ||| (off <<< (16 + 3 * nw + 8 * n))
    recs := recs.push R
    cnts := cnts.push c
    if withTr then
      for k in [0:c] do
        trs := trs.push (pack w tr[k]!)
        tris := tris.push (pack w (inv n tr[k]!))
  return (recs, cnts, trs, tris)

structure Ctx where
  P : Name
  n : Nat
  w : Nat
  kS : Nat
  nb : Nat

meta def Ctx.nE (c : Ctx) : Expr := lit c.n
meta def Ctx.wE (c : Ctx) : Expr := lit c.w
meta def Ctx.mE (c : Ctx) : Expr := mkApp (mkConst ``CFSG.KS.mask) c.wE
meta def Ctx.nwE (c : Ctx) : Expr := mulE c.nE c.wE
meta def Ctx.pmE (c : Ctx) : Expr := mkApp (mkConst ``CFSG.KS.mask) c.nwE
meta def Ctx.idE (c : Ctx) : Expr := mkApp2 (mkConst ``CFSG.KC.Enum.pidn) c.nE c.wE
meta def Ctx.k (c : Ctx) (s : Name) : Expr := mkConst (c.P ++ s)
meta def Ctx.steps (c : Ctx) (iE : Expr) : Expr :=
  mkAppN (mkConst ``CFSG.KS.Raw.stepsAt) #[c.nE, c.wE, c.k `S, lit c.kS, c.k `BP, iE]
meta def Ctx.root (c : Ctx) (iE : Expr) : Expr :=
  mkAppN (mkConst ``CFSG.KC.Enum.pg) #[c.wE, c.mE, c.k `BP, iE]

meta def forallLt (k : Expr) (body : Expr → Expr) : Expr :=
  mkForall `i .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, k]) (body (mkBVar 1)))

meta def ctxOf (P : Name) : CommandElabM Ctx := do
  return { P, n := ← natOf (P ++ `pn), w := ← natOf (P ++ `pw), kS := ← natOf (P ++ `pkS),
           nb := ← natOf (P ++ `pnb) }

meta def orbSlT (c : Ctx) (LCH : Nat) (iE sE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvOrbSlK)
    #[c.nE, c.wE, c.mE, c.nwE, c.k `S, c.k `SI, lit c.kS, c.steps iE, mkApp (c.k `LR) iE,
      mulE sE (lit LCH), lit LCH])

meta def orbHdT (c : Ctx) (iE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvOrbHdK)
    #[c.nE, c.wE, c.mE, lit c.kS, c.root iE, c.steps iE, mkApp (c.k `LR) iE])

meta def lvHdT (c : Ctx) (iE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvHdK)
    #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `TR, lit c.kS, c.root iE, c.steps iE, mkApp (c.k `LR) iE])

meta def lvSlT (c : Ctx) (LCH : Nat) (iE sE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvSlK)
    #[c.nE, c.wE, c.mE, c.nwE, c.k `S, c.k `SI, c.k `TR, c.k `TRI, lit c.kS, c.steps iE,
      mkApp (c.k `LR) iE, mulE sE (lit LCH), lit LCH])

meta def lvT (c : Ctx) (iE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.levelK)
    #[c.nE, c.wE, c.mE, c.nwE, c.pmE, c.idE, c.k `S, c.k `SI, c.k `TR, c.k `TRI, lit c.kS,
      c.root iE, c.steps iE, mkApp (c.k `LR) iE])

meta def schT (c : Ctx) (CH : Nat) (iE sE : Expr) : Expr :=
  isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schK)
    #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, lit c.kS,
      c.k `BP, lit c.nb, iE, c.steps iE, mulE sE (lit CH), lit CH])

meta def addRefl (nm : Name) (ty : Expr) : CoreM Unit :=
  addThm nm ty reflBoolTrue

meta def setup (P : Name) (n w : Nat) (sId bId : Ident) :
    CommandElabM (Array (Array Nat) × Array Nat) := do
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let S ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) sN
  let base ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  withSync do
    addDef (P ++ `pn) natT (lit n)
    addDef (P ++ `pw) natT (lit w)
    addDef (P ++ `pkS) natT (lit S.size)
    addDef (P ++ `pnb) natT (lit base.size)
  return (S, base)

meta def addHead (c : Ctx) (kO : Nat) (dN : Name) : CoreM Unit :=
  addRefl (c.P ++ `head) (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.headK)
    #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, lit c.kS, lit kO, mkConst dN, lit c.nb,
      c.k `BP]))

end CFSG.KS.RawGenSplit

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#ks_raworb_data " pre:ident nn:num ww:num lch:num sId:ident bId:ident ko:num dId:ident :
    command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let LCH := lch.getNat
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let (S, base) ← setup P n w sId bId
  let (recs, _, _, _) := levels n w S base false
  let c : Ctx := { P, n, w, kS := S.size, nb := base.size }
  withSync do
    addDef (P ++ `pLCH) natT (lit LCH)
    addDef (P ++ `NL) natT (lit ((n + LCH - 1) / LCH))
    addTree (P ++ `S) (S.map (pack w))
    addTree (P ++ `SI) ((S.map (inv n)).map (pack w))
    addTree (P ++ `LR) recs
    addDef (P ++ `BP) natT (lit (pack w base))
    addHead c (ko.getNat) dN
    for i in [0:c.nb] do
      addRefl (P ++ Name.mkSimple s!"lh{i}") (orbHdT c (lit i))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#ks_raworb_sl " pre:ident ii:num lo:num hi:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let LCH ← natOf (P ++ `pLCH)
  withSync do
    for s in [lo.getNat:hi.getNat] do
      addRefl (P ++ Name.mkSimple s!"ls{ii.getNat}_{s}") (orbSlT c LCH (lit ii.getNat) (lit s))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#ks_raworb_join " pre:ident : command => do
  let P := pre.getId
  let c ← ctxOf P
  let LCH ← natOf (P ++ `pLCH)
  let NL ← natOf (P ++ `NL)
  let lhP := mkLambda `i .default natT (orbHdT c (mkBVar 0))
  let hlhV := forallChain lhP c.nb fun i => mkConst (P ++ Name.mkSimple s!"lh{i}")
  let innerP := fun (iE : Expr) => mkLambda `s .default natT (orbSlT c LCH iE (mkBVar 0))
  let outerBody := fun (iE : Expr) => forallLt (lit NL) fun sE =>
    orbSlT c LCH (iE.liftLooseBVars 0 2) sE
  let outerP := mkLambda `i .default natT (outerBody (mkBVar 0))
  let hlsV := forallChain outerP c.nb fun i =>
    forallChain (innerP (lit i)) NL fun s => mkConst (P ++ Name.mkSimple s!"ls{i}_{s}")
  let hoT := mkAppN (mkConst ``CFSG.KS.Raw.OrbsOK)
    #[c.nE, c.wE, c.k `S, c.k `SI, c.k `LR, lit c.kS, lit c.nb, c.k `BP, lit NL, lit LCH]
  let lhAll := forallLt (lit c.nb) fun iE => orbHdT c iE
  let lsAll := forallLt (lit c.nb) fun iE => outerBody iE
  let hoV := mkAppN (mkConst ``And.intro) #[lhAll, lsAll, hlhV, hlsV]
  withSync do
    addThm (P ++ `ho) hoT hoV

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#ks_rawchain_sl2_data " pre:ident nn:num ww:num ch:num lch:num sId:ident bId:ident ko:num
    dId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let CH := ch.getNat
  let LCH := lch.getNat
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let (S, base) ← setup P n w sId bId
  let (recs, cnts, trs, tris) := levels n w S base true
  let c : Ctx := { P, n, w, kS := S.size, nb := base.size }
  withSync do
    addDef (P ++ `pLCH) natT (lit LCH)
    addDef (P ++ `pCH) natT (lit CH)
    addDef (P ++ `NL) natT (lit ((n + LCH - 1) / LCH))
    addDef (P ++ `NS) natT (lit (if CH == 0 then 0 else (n + CH - 1) / CH))
    for i in [0:base.size] do
      addDef (P ++ Name.mkSimple s!"NS{i}") natT
        (lit (if CH == 0 then 0 else (cnts[i]! + CH - 1) / CH))
    addTree (P ++ `S) (S.map (pack w))
    addTree (P ++ `SI) ((S.map (inv n)).map (pack w))
    addTree (P ++ `LR) recs
    addTree (P ++ `TR) trs
    addTree (P ++ `TRI) tris
    addDef (P ++ `BP) natT (lit (pack w base))
    addHead c (ko.getNat) dN
    for i in [0:c.nb] do
      addRefl (P ++ Name.mkSimple s!"lh{i}") (lvHdT c (lit i))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#ks_rawchain_sl2_lv " pre:ident ii:num lo:num hi:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let LCH ← natOf (P ++ `pLCH)
  withSync do
    for s in [lo.getNat:hi.getNat] do
      addRefl (P ++ Name.mkSimple s!"ls{ii.getNat}_{s}") (lvSlT c LCH (lit ii.getNat) (lit s))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#ks_rawchain_sl2_sch " pre:ident ii:num lo:num hi:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let CH ← natOf (P ++ `pCH)
  withSync do
    for s in [lo.getNat:hi.getNat] do
      addRefl (P ++ Name.mkSimple s!"sch{ii.getNat}_{s}") (schT c CH (lit ii.getNat) (lit s))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#ks_rawchain_sl2_join " pre:ident : command => do
  let P := pre.getId
  let c ← ctxOf P
  let LCH ← natOf (P ++ `pLCH)
  let CH ← natOf (P ++ `pCH)
  let NL ← natOf (P ++ `NL)
  let NS ← natOf (P ++ `NS)
  let mut nsi : Array Nat := #[]
  for i in [0:c.nb] do
    nsi := nsi.push (← natOf (P ++ Name.mkSimple s!"NS{i}"))
  withSync do
    for i in [0:c.nb] do
      let iE := lit i
      let slP := mkLambda `s .default natT (lvSlT c LCH iE (mkBVar 0))
      let hsV := forallChain slP NL fun s => mkConst (P ++ Name.mkSimple s!"ls{i}_{s}")
      let hN := mkApp2 (mkConst ``Nat.le_of_ble_eq_true) c.nE (mulE (lit NL) (lit LCH))
      let hNV := mkApp hN (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
      let v := mkAppN (mkConst ``CFSG.KS.Raw.levelK_of_sl)
        #[c.nE, c.wE, c.mE, c.nwE, c.pmE, c.idE, lit c.kS, c.root iE, c.steps iE,
          mkApp (c.k `LR) iE, lit NL, lit LCH, c.k `S, c.k `SI, c.k `TR, c.k `TRI,
          mkConst (P ++ Name.mkSimple s!"lh{i}"), hsV, hNV]
      let nm := P ++ Name.mkSimple s!"lv{i}"
      addThm nm (lvT c iE) v
    let lvP := mkLambda `i .default natT (lvT c (mkBVar 0))
    let hlV := forallChain lvP c.nb fun i => mkConst (P ++ Name.mkSimple s!"lv{i}")
    let hlT := mkAppN (mkConst ``CFSG.KS.Raw.LevelsOK)
      #[c.nE, c.wE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI, lit c.kS, lit c.nb, c.k `BP]
    addThm (P ++ `hl) hlT hlV
    if CH != 0 then
      let innerP := fun (iE : Expr) => mkLambda `s .default natT (schT c CH iE (mkBVar 0))
      let outerBody := fun (iE : Expr) => forallLt (lit NS) fun sE =>
        schT c CH (iE.liftLooseBVars 0 2) sE
      let outerP := mkLambda `i .default natT (outerBody (mkBVar 0))
      let hsV := forallChain outerP c.nb fun i =>
        let iE := lit i
        let hc := mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true)
            (mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (c.k `LR) iE)) (mulE (lit nsi[i]!) (lit CH)))
          (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
        let inner := forallChain (innerP iE) nsi[i]! fun s => mkConst (P ++ Name.mkSimple s!"sch{i}_{s}")
        mkAppN (mkConst ``CFSG.KS.Raw.schK_slices)
          #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI,
            lit c.kS, c.k `BP, lit c.nb, iE, c.steps iE, lit NS, lit nsi[i]!, lit CH, hc, inner]
      let hsT := forallLt (lit c.nb) fun iE => outerBody iE
      addThm (P ++ `hs) hsT hsV

end
