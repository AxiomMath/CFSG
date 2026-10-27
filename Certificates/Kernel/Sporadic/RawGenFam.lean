module

public import CFSG.Certificates.Kernel.Spor.RawFam
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.KS.RawGenFam

open CFSG.KC.Tab CFSG.KS.RawGen

meta def leE (a b : Expr) : Expr :=
  mkAppN (mkConst ``LE.le [0]) #[natT, mkConst ``instLENat, a, b]

meta def emit (P : Name) (n w CH : Nat) (S : Array (Array Nat)) (base : Array Nat) (kO : Nat)
    (dE : Expr) : CoreM Unit := do
  let kS := S.size
  let nb := base.size
  let Sinv := S.map (inv n)
  let mut recs : Array Nat := #[]
  let mut trs : Array Nat := #[]
  let mut tris : Array Nat := #[]
  let nw := n * w
  for i in [0:nb] do
    let idx := (List.range kS).filter fun j => (List.range i).all fun t =>
      (S[j]!)[base[t]!]! == base[t]!
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
    for k in [0:c] do
      trs := trs.push (pack w tr[k]!)
      tris := tris.push (pack w (inv n tr[k]!))
  let BP := pack w base
  let NS := (n + CH - 1) / CH
  addTree (P ++ `S) (S.map (pack w))
  addTree (P ++ `SI) (Sinv.map (pack w))
  addTree (P ++ `LR) recs
  addTree (P ++ `TR) trs
  addTree (P ++ `TRI) tris
  addDef (P ++ `BP) natT (lit BP)
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
    #[nE, wE, mE, nwE, idE, c `S, c `SI, kSE, lit kO, dE, nbE, c `BP])
  addThm (P ++ `head) headT reflBoolTrue
  let stepsE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KS.Raw.stepsAt) #[nE, wE, c `S, kSE, c `BP, iE]
  let lvT := fun (iE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.levelK)
    #[nE, wE, mE, nwE, pmE, idE, c `S, c `SI, c `TR, c `TRI, kSE,
      mkAppN (mkConst ``CFSG.KC.Enum.pg) #[wE, mE, c `BP, iE], stepsE iE, mkApp (c `LR) iE])
  for i in [0:nb] do
    let nm := P ++ Name.mkSimple s!"lv{i}"
    addThm nm (lvT (lit i)) reflBoolTrue
  let lvP := mkLambda `i .default natT (lvT (mkBVar 0))
  let hlV := forallChain lvP nb fun i => mkConst (P ++ Name.mkSimple s!"lv{i}")
  let hlT := mkAppN (mkConst ``CFSG.KS.Raw.LevelsOK)
    #[nE, wE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, nbE, c `BP]
  addThm (P ++ `hl) hlT hlV
  let schT := fun (iE sE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schK)
    #[nE, wE, mE, nwE, idE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, c `BP, nbE, iE, stepsE iE,
      mulE sE (lit CH), lit CH])
  for i in [0:nb] do
    for s in [0:NS] do
      let nm := P ++ Name.mkSimple s!"sch{i}_{s}"
      let ty := schT (lit i) (lit s)
      addThm nm ty reflBoolTrue
  let innerP := fun (iE : Expr) => mkLambda `s .default natT (schT iE (mkBVar 0))
  let outerBody := fun (iE : Expr) =>
    mkForall `s .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit NS])
      (schT (iE.liftLooseBVars 0 2) (mkBVar 1)))
  let outerP := mkLambda `i .default natT (outerBody (mkBVar 0))
  let hsV := forallChain outerP nb fun i =>
    forallChain (innerP (lit i)) NS fun s => mkConst (P ++ Name.mkSimple s!"sch{i}_{s}")
  let hsT := mkForall `i .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, nbE])
    (outerBody (mkBVar 1)))
  addThm (P ++ `hs) hsT hsV
  let nsLe := leE nE (mulE (lit NS) (lit CH))
  let nsV := mkApp3 (mkConst ``of_decide_eq_true) nsLe
    (mkApp2 (mkConst ``Nat.decLe) nE (mulE (lit NS) (lit CH)))
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  addThm (P ++ `hNS) nsLe nsV
  let okT := mkAppN (mkConst ``CFSG.KS.Raw.RawK)
    #[nE, wE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, lit kO, dE, nbE, c `BP, lit NS, lit CH]
  let okV := mkAppN (mkConst ``And.intro)
    #[headT, mkAppN (mkConst ``And) #[hlT, mkAppN (mkConst ``And) #[nsLe, hsT]], c `head,
      mkAppN (mkConst ``And.intro) #[hlT, mkAppN (mkConst ``And) #[nsLe, hsT], c `hl,
        mkAppN (mkConst ``And.intro) #[nsLe, hsT, c `hNS, c `hs]]]
  addThm (P ++ `ok) okT okV

end CFSG.KS.RawGenFam

open CFSG.KC.Tab CFSG.KS.RawGenFam in
elab "#ks_rawchain_fam " pre:ident nn:num ww:num ch:num sId:ident bId:ident kId:ident dId:ident :
    command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let kN ← liftCoreM <| realizeGlobalConstNoOverload kId
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let SF ← liftTermElabM <| unsafe evalConst (List (List (List Nat))) sN
  let BF ← liftTermElabM <| unsafe evalConst (List (List Nat)) bN
  let KF ← liftTermElabM <| unsafe evalConst (List Nat) kN
  unless SF.length == BF.length && SF.length == KF.length do
    throwError "#ks_rawchain_fam: the families have different lengths"
  let wordTy := mkApp (mkConst ``List [0]) (mkConst ``Int)
  let eltTy := mkApp (mkConst ``List [0]) wordTy
  let n := nn.getNat
  let w := ww.getNat
  let CH := ch.getNat
  let N := SF.length
  if N == 0 then throwError "#ks_rawchain_fam: the family is empty"
  let cN := fun (i : Nat) (s : Name) => (P ++ Name.mkSimple s!"c{i}") ++ s
  let dAt := fun (kE : Expr) => mkAppN (mkConst ``List.getD [0]) #[eltTy, mkConst dN, kE,
    mkApp (mkConst ``List.nil [0]) wordTy]
  liftCoreM <| withOptions (Elab.async.set · false) do
    for i in [0:N] do
      let S := (SF[i]!.map List.toArray).toArray
      let base := BF[i]!.toArray
      emit (P ++ Name.mkSimple s!"c{i}") n w CH S base KF[i]! (dAt (lit i))
    let sel := fun (ty : Expr) (leaf : Nat → Expr) => Id.run do
      let mut e := leaf (N - 1)
      for j' in [1:N] do
        let j := N - 1 - j'
        e := mkAppN (mkConst ``cond [1]) #[ty,
          mkApp2 (mkConst ``Nat.beq) (mkBVar 0) (lit j), leaf j, e]
      return mkLambda `k .default natT e
    for s in [`S, `SI, `LR, `TR, `TRI] do
      addDef (P ++ s) (mkForall `k .default natT fnT) (sel fnT fun j => mkConst (cN j s))
    addDef (P ++ `BP) fnT (sel natT fun j => mkConst (cN j `BP))
    addDef (P ++ `kS) fnT (sel natT fun j => lit SF[j]!.length)
    addDef (P ++ `kO) fnT (sel natT fun j => lit KF[j]!)
    addDef (P ++ `nb) fnT (sel natT fun j => lit BF[j]!.length)
    addDef (P ++ `NS) fnT (sel natT fun j => lit ((n + CH - 1) / CH))
    let rawAt := fun (kE : Expr) => mkAppN (mkConst ``CFSG.KS.Raw.RawK)
      #[lit n, lit w, mkApp (mkConst (P ++ `S)) kE, mkApp (mkConst (P ++ `SI)) kE,
        mkApp (mkConst (P ++ `LR)) kE, mkApp (mkConst (P ++ `TR)) kE,
        mkApp (mkConst (P ++ `TRI)) kE, mkApp (mkConst (P ++ `kS)) kE,
        mkApp (mkConst (P ++ `kO)) kE, dAt kE, mkApp (mkConst (P ++ `nb)) kE,
        mkApp (mkConst (P ++ `BP)) kE, mkApp (mkConst (P ++ `NS)) kE, lit CH]
    let allP := mkLambda `k .default natT (rawAt (mkBVar 0))
    let allV := CFSG.KS.RawGen.forallChain allP N fun i => mkConst (cN i `ok)
    let allT := mkForall `k .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit N])
      (rawAt (mkBVar 1)))
    CFSG.KS.RawGen.addThm (P ++ `all) allT allV
    addDef (P ++ `N) natT (lit N)

end
