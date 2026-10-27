module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.SchTriv
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#ks_rawchain_sl2 " pre:ident nn:num ww:num ch:num lch:num lm:num sId:ident bId:ident ko:num
    dId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let CH := ch.getNat
  let LCH := lch.getNat
  let lim := lm.getNat
  let kO := ko.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let S ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) sN
  let base ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  let kS := S.size
  let nb := base.size
  let Sinv := S.map (inv n)
  let mut recs : Array Nat := #[]
  let mut cnts : Array Nat := #[]
  let mut trs : Array Nat := #[]
  let mut tris : Array Nat := #[]
  let nw := n * w
  for i in [0:nb] do
    let idx := (List.range kS).filter fun j => (List.range i).all fun t => (S[j]!)[base[t]!]! == base[t]!
    let steps := (idx.map fun j => S[j]!).toArray ++ (idx.map fun j => Sinv[j]!).toArray
    let root := base[i]!
    let mut pos : Array Nat := (Array.replicate n n).set! root 0
    let mut pts : Array Nat := #[root]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    let mut tr : Array (Array Nat) := #[Array.range n]
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
            tr := tr.push (comp n s tr[h]!)
    let off := trs.size
    let c := pts.size
    let pad := fun (a : Array Nat) => a ++ Array.replicate (n - a.size) 0
    let mut R := c
    R := R ||| (pack w (pad pts) <<< 16)
    R := R ||| (pack w pos <<< (16 + nw))
    R := R ||| (pack w (pad par) <<< (16 + 2 * nw))
    R := R ||| (pack 8 (pad lab) <<< (16 + 3 * nw))
    R := R ||| (off <<< (16 + 3 * nw + 8 * n))
    recs := recs.push R
    cnts := cnts.push c
    for k in [0:c] do
      trs := trs.push (pack w tr[k]!)
      tris := tris.push (pack w (inv n tr[k]!))
  let BP := pack w base
  let NS := (n + CH - 1) / CH
  let NL := (n + LCH - 1) / LCH
  let natE := natT
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `S) (S.map (pack w))
    addTree (P ++ `SI) (Sinv.map (pack w))
    addTree (P ++ `LR) recs
    addTree (P ++ `TR) trs
    addTree (P ++ `TRI) tris
    addDef (P ++ `BP) natE (lit BP)
    let nE := lit n
    let wE := lit w
    let mE := mkApp (mkConst ``CFSG.KS.mask) wE
    let nwE := mulE nE wE
    let pmE := mkApp (mkConst ``CFSG.KS.mask) nwE
    let idE := mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE
    let c := fun (s : Name) => mkConst (P ++ s)
    let kSE := lit kS
    let nbE := lit nb
    let headT := isTrue (mkAppN (mkConst ``CFSG.KS.Raw.headK)
      #[nE, wE, mE, nwE, idE, c `S, c `SI, kSE, lit kO, mkConst dN, nbE, c `BP])
    if lim == 0 then
      addThm (P ++ `head) headT reflBoolTrue
    let stepsE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KS.Raw.stepsAt) #[nE, wE, c `S, kSE, c `BP, iE]
    let rootE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KC.Enum.pg) #[wE, mE, c `BP, iE]
    let lvT := fun (iE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.levelK)
      #[nE, wE, mE, nwE, pmE, idE, c `S, c `SI, c `TR, c `TRI, kSE, rootE iE, stepsE iE,
        mkApp (c `LR) iE])
    for i in [0:nb] do
      let iE := lit i
      let lhT := isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvHdK)
        #[nE, wE, mE, nwE, idE, c `TR, kSE, rootE iE, stepsE iE, mkApp (c `LR) iE])
      let lhN := P ++ Name.mkSimple s!"lh{i}"
      addThm lhN lhT reflBoolTrue
      let slP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvSlK)
        #[nE, wE, mE, nwE, c `S, c `SI, c `TR, c `TRI, kSE, stepsE iE, mkApp (c `LR) iE,
          mulE (mkBVar 0) (lit LCH), lit LCH]))
      let cnt := if lim == 0 then NL else min lim NL
      for s in [0:cnt] do
        let nm := P ++ Name.mkSimple s!"ls{i}_{s}"
        addThm nm (mkApp slP (lit s)).headBeta reflBoolTrue
      if lim == 0 then
        let hsV := forallChain slP NL fun s => mkConst (P ++ Name.mkSimple s!"ls{i}_{s}")
        let hN := mkApp2 (mkConst ``Nat.le_of_ble_eq_true) nE (mulE (lit NL) (lit LCH))
        let hNV := mkApp hN (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
        let v := mkAppN (mkConst ``CFSG.KS.Raw.levelK_of_sl)
          #[nE, wE, mE, nwE, pmE, idE, kSE, rootE iE, stepsE iE, mkApp (c `LR) iE, lit NL, lit LCH,
            c `S, c `SI, c `TR, c `TRI, mkConst lhN, hsV, hNV]
        addThm (P ++ Name.mkSimple s!"lv{i}") (lvT iE) v
    let schT := fun (iE sE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schK)
      #[nE, wE, mE, nwE, idE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, c `BP, nbE, iE, stepsE iE,
        mulE sE (lit CH), lit CH])
    if lim > 0 then
      for s in [0:min lim NS] do
        let nm := P ++ Name.mkSimple s!"sch0_{s}"
        addThm nm (schT (lit 0) (lit s)) reflBoolTrue
      return
    let lvP := mkLambda `i .default natE (lvT (mkBVar 0))
    let hlV := forallChain lvP nb fun i => mkConst (P ++ Name.mkSimple s!"lv{i}")
    let hlT := mkAppN (mkConst ``CFSG.KS.Raw.LevelsOK) #[nE, wE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, nbE, c `BP]
    addThm (P ++ `hl) hlT hlV
    if CH == 0 then return
    let NSi := fun (i : Nat) => (cnts[i]! + CH - 1) / CH
    for i in [0:nb] do
      for s in [0:NSi i] do
        let nm := P ++ Name.mkSimple s!"sch{i}_{s}"
        addThm nm (schT (lit i) (lit s)) reflBoolTrue
    let innerP := fun (iE : Expr) => mkLambda `s .default natE (schT iE (mkBVar 0))
    let outerBody := fun (iE : Expr) =>
      mkForall `s .default natE (mkForall `h .default
        (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, lit NS])
        (schT (iE.liftLooseBVars 0 2) (mkBVar 1)))
    let outerP := mkLambda `i .default natE (outerBody (mkBVar 0))
    let hsV := forallChain outerP nb fun i =>
      let iE := lit i
      let hc := mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true) (mkApp (c `LR) iE |> fun e =>
          mkApp (mkConst ``CFSG.KS.Raw.rcnt) e) (mulE (lit (NSi i)) (lit CH)))
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
      let inner := forallChain (innerP iE) (NSi i) fun s => mkConst (P ++ Name.mkSimple s!"sch{i}_{s}")
      mkAppN (mkConst ``CFSG.KS.Raw.schK_slices)
        #[nE, wE, mE, nwE, idE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, c `BP, nbE, iE, stepsE iE,
          lit NS, lit (NSi i), lit CH, hc, inner]
    let hsT := mkForall `i .default natE (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, nbE])
      (outerBody (mkBVar 1)))
    addThm (P ++ `hs) hsT hsV
    addDef (P ++ `NS) natE (lit NS)
