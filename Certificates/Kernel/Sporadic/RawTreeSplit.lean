module

public import Certificates.Kernel.Sporadic.RawTreeGen
public meta import Certificates.Kernel.Sporadic.RawTreeGen
public meta import Certificates.Kernel.Sporadic.RawGenSplit
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public import Certificates.Kernel.Sporadic.RawGenSplit

open Lean Elab Command

public section

namespace CFSG.KS.RawTreeSplit

open CFSG.KC.Tab CFSG.KS.RawGen

structure Ctx where
  P : Name
  n : Nat
  w : Nat
  kS : Nat
  nb : Nat
  CH : Nat

meta def ctxOf (P : Name) : CommandElabM Ctx := do
  let f := fun (s : Name) => CFSG.KS.RawGenSplit.natOf (P ++ s)
  return { P, n := ← f `pn, w := ← f `pw, kS := ← f `pkS, nb := ← f `pnb, CH := ← f `pCH }

meta def schP (c : Ctx) (iE : Expr) : Expr :=
  let k := fun (s : Name) => mkConst (c.P ++ s)
  let nE := lit c.n
  let wE := lit c.w
  mkLambda `s .default natT (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schBK)
    #[nE, wE, mkApp (mkConst ``CFSG.KS.mask) wE, mulE nE wE, lit c.nb, k `S, k `SI, k `LR, k `ST,
      lit c.kS, k `BP, iE, mulE (mkBVar 0) (lit c.CH), lit c.CH]))

end CFSG.KS.RawTreeSplit

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawTreeGen in
elab "#ks_rawtree_data " pre:ident nn:num ww:num ch:num lch:num sId:ident bId:ident ko:num
    dId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let CH := ch.getNat
  let LCH := lch.getNat
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
  let mut sts : Array Nat := #[]
  let nw := n * w
  for i in [0:nb] do
    let idx := (List.range kS).filter fun j => (List.range i).all fun t => (S[j]!)[base[t]!]! == base[t]!
    let steps := (idx.map fun j => S[j]!).toArray ++ (idx.map fun j => Sinv[j]!).toArray
    let letters := idx.toArray ++ (idx.map fun j => j + kS).toArray
    let mut T := letters.size
    for c in [0:letters.size] do
      T := T ||| (letters[c]! <<< (8 + 8 * c))
    sts := sts.push T
    let root := base[i]!
    let mut pos : Array Nat := (Array.replicate n n).set! root 0
    let mut pts : Array Nat := #[root]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
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
    let c := pts.size
    let pad := fun (a : Array Nat) => a ++ Array.replicate (n - a.size) 0
    let mut R := c
    R := R ||| (pack w (pad pts) <<< 16)
    R := R ||| (pack w pos <<< (16 + nw))
    R := R ||| (pack w (pad par) <<< (16 + 2 * nw))
    R := R ||| (pack 8 (pad lab) <<< (16 + 3 * nw))
    recs := recs.push R
    cnts := cnts.push c
  let BP := pack w base
  let NL := (n + LCH - 1) / LCH
  let natE := natT
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `pn) natE (lit n)
    addDef (P ++ `pw) natE (lit w)
    addDef (P ++ `pkS) natE (lit kS)
    addDef (P ++ `pnb) natE (lit nb)
    addDef (P ++ `pCH) natE (lit CH)
    for i in [0:nb] do
      addDef (P ++ Name.mkSimple s!"NS{i}") natE (lit ((cnts[i]! + CH - 1) / CH))
    addTree (P ++ `S) (S.map (pack w))
    addTree (P ++ `SI) (Sinv.map (pack w))
    addTree (P ++ `LR) recs
    addTree (P ++ `ST) sts
    addDef (P ++ `BP) natE (lit BP)
    let nE := lit n
    let wE := lit w
    let mE := mkApp (mkConst ``CFSG.KS.mask) wE
    let nwE := mulE nE wE
    let idE := mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE
    let c := fun (s : Name) => mkConst (P ++ s)
    let kSE := lit kS
    let nbE := lit nb
    let lt := fun (a b : Expr) => mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, a, b]
    let headT := isTrue (mkAppN (mkConst ``CFSG.KS.Raw.headK)
      #[nE, wE, mE, nwE, idE, c `S, c `SI, kSE, lit kO, mkConst dN, nbE, c `BP])
    let stepsE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KS.Raw.stepsAt) #[nE, wE, c `S, kSE, c `BP, iE]
    let rootE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KC.Enum.pg) #[wE, mE, c `BP, iE]
    let stT := isTrue (mkAppN (mkConst ``CFSG.KC.Enum.allN) #[nbE, mkLambda `l .default natE
      (mkAppN (mkConst ``Nat.beq) #[mkApp (c `ST) (mkBVar 0), stepsE (mkBVar 0)])])
    addThm (P ++ `head) headT reflBoolTrue
    addThm (P ++ `st) stT reflBoolTrue
    let lhT := fun (iE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvHdTK)
      #[nE, wE, mE, kSE, rootE iE, stepsE iE, mkApp (c `LR) iE])
    let slP := fun (iE : Expr) => mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvSlTK)
      #[nE, wE, mE, nwE, c `S, c `SI, kSE, stepsE iE, mkApp (c `LR) iE,
        mulE (mkBVar 0) (lit LCH), lit LCH]))
    let mut tlPf : Array Expr := #[]
    for i in [0:nb] do
      let iE := lit i
      let lhN := P ++ Name.mkSimple s!"lh{i}"
      addThm lhN (lhT iE) reflBoolTrue
      for s in [0:NL] do
        addThm (P ++ Name.mkSimple s!"ls{i}_{s}") (mkApp (slP iE) (lit s)).headBeta reflBoolTrue
      let hsV := forallChain (slP iE) NL fun s => mkConst (P ++ Name.mkSimple s!"ls{i}_{s}")
      let hNV := mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true) nE (mulE (lit NL) (lit LCH)))
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
      tlPf := tlPf.push (mkAppN (mkConst ``CFSG.KS.Raw.treeLv_of_sl)
        #[nE, wE, mE, nwE, kSE, rootE iE, stepsE iE, mkApp (c `LR) iE, lit NL, lit LCH,
          c `S, c `SI, mkConst lhN, hsV, hNV])
    let tlBody := fun (iE : Expr) => mkAppN (mkConst ``And) #[lhT iE,
      mkForall `k .default natE (mkForall `h .default (lt (mkBVar 0) nE)
        (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvPtTK) #[nE, wE, mE, nwE, c `S, c `SI, kSE,
          stepsE (iE.liftLooseBVars 0 2), mkApp (c `LR) (iE.liftLooseBVars 0 2),
          mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (c `LR) (iE.liftLooseBVars 0 2)),
          mkApp (mkConst ``CFSG.KS.Raw.stCnt) (stepsE (iE.liftLooseBVars 0 2)), mkBVar 1])))]
    let tlV := forallChain (mkLambda `i .default natE (tlBody (mkBVar 0))) nb fun i => tlPf[i]!
    let tlT := mkAppN (mkConst ``CFSG.KS.Raw.TreeOK) #[nE, wE, c `S, c `SI, c `LR, kSE, nbE, c `BP]
    addThm (P ++ `tl) tlT tlV
    let hstT := mkAppN (mkConst ``CFSG.KS.Raw.StepsOK) #[nE, wE, c `S, c `ST, kSE, nbE, c `BP]
    let hstV := mkAppN (mkConst ``CFSG.KS.Raw.stepsOK_of) #[nE, wE, c `S, c `ST, kSE, nbE, c `BP,
      mkConst (P ++ `st)]
    addThm (P ++ `hst) hstT hstV

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawTreeGen CFSG.KS.RawTreeSplit in
elab "#ks_rawtree_sch " pre:ident ii:num lo:num hi:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let iE := lit ii.getNat
  liftCoreM <| withOptions (Elab.async.set · false) do
    for s in [lo.getNat:hi.getNat] do
      addThm (P ++ Name.mkSimple s!"sch{ii.getNat}_{s}") (mkApp (schP c iE) (lit s)).headBeta
        reflBoolTrue

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawTreeGen CFSG.KS.RawTreeSplit in
elab "#ks_rawtree_join " pre:ident : command => do
  let P := pre.getId
  let c ← ctxOf P
  let mut nsi : Array Nat := #[]
  for i in [0:c.nb] do
    nsi := nsi.push (← CFSG.KS.RawGenSplit.natOf (P ++ Name.mkSimple s!"NS{i}"))
  let natE := natT
  let nE := lit c.n
  let wE := lit c.w
  let mE := mkApp (mkConst ``CFSG.KS.mask) wE
  let nwE := mulE nE wE
  let k := fun (s : Name) => mkConst (P ++ s)
  let kSE := lit c.kS
  let nbE := lit c.nb
  let CH := c.CH
  let lt := fun (a b : Expr) => mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, a, b]
  liftCoreM <| withOptions (Elab.async.set · false) do
    let mut hsPf : Array Expr := #[]
    for i in [0:c.nb] do
      let iE := lit i
      let inner := forallChain (schP c iE) nsi[i]! fun s => mkConst (P ++ Name.mkSimple s!"sch{i}_{s}")
      let hc := mkApp (mkApp2 (mkConst ``Nat.le_of_ble_eq_true)
          (mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (k `LR) iE)) (mulE (lit nsi[i]!) (lit CH)))
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
      hsPf := hsPf.push (mkAppN (mkConst ``CFSG.KS.Raw.schB_of_sl)
        #[nE, wE, mE, nwE, nbE, kSE, k `BP, iE, lit nsi[i]!, lit CH, k `S, k `SI, k `LR, k `ST,
          hc, inner])
    let hsBody := fun (iE : Expr) => mkForall `h .default natE (mkForall `hh .default
      (lt (mkBVar 0) (mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp (k `LR) (iE.liftLooseBVars 0 1))))
      (isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schBPt) #[nE, wE, mE, nwE, nbE, k `S, k `SI, k `LR,
        k `ST, kSE, k `BP, iE.liftLooseBVars 0 2, mkBVar 1])))
    let hsV := forallChain (mkLambda `i .default natE (hsBody (mkBVar 0))) c.nb fun i => hsPf[i]!
    let hsT := mkAppN (mkConst ``CFSG.KS.Raw.SchBOK) #[nE, wE, nbE, k `S, k `SI, k `LR, k `ST, kSE,
      k `BP]
    addThm (P ++ `hs) hsT hsV

end
