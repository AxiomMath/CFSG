module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Mathlib.GroupTheory.Schreier

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#ks_raworb " pre:ident nn:num ww:num lch:num sId:ident bId:ident ko:num dId:ident :
    command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
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
  let nw := n * w
  for i in [0:nb] do
    let idx := (List.range kS).filter fun j => (List.range i).all fun t => (S[j]!)[base[t]!]! == base[t]!
    let steps := (idx.map fun j => S[j]!).toArray ++ (idx.map fun j => Sinv[j]!).toArray
    let root := base[i]!
    let mut pos : Array Nat := (Array.replicate n n).set! root 0
    let mut pts : Array Nat := #[root]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    for h in [0:n] do
      if h < pts.size then
        let x := pts[h]!
        for j in [0:steps.size] do
          let y := (steps[j]!)[x]!
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
  let BP := pack w base
  let NL := (n + LCH - 1) / LCH
  let natE := natT
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `S) (S.map (pack w))
    addTree (P ++ `SI) (Sinv.map (pack w))
    addTree (P ++ `LR) recs
    addDef (P ++ `BP) natE (lit BP)
    let nE := lit n
    let wE := lit w
    let mE := mkApp (mkConst ``CFSG.KS.mask) wE
    let nwE := mulE nE wE
    let idE := mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE
    let c := fun (s : Name) => mkConst (P ++ s)
    let kSE := lit kS
    let nbE := lit nb
    let headT := isTrue (mkAppN (mkConst ``CFSG.KS.Raw.headK)
      #[nE, wE, mE, nwE, idE, c `S, c `SI, kSE, lit kO, mkConst dN, nbE, c `BP])
    addThm (P ++ `head) headT reflBoolTrue
    let stepsE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KS.Raw.stepsAt) #[nE, wE, c `S, kSE, c `BP, iE]
    let rootE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KC.Enum.pg) #[wE, mE, c `BP, iE]
    let lhT := fun (iE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvOrbHdK)
      #[nE, wE, mE, kSE, rootE iE, stepsE iE, mkApp (c `LR) iE])
    let lsT := fun (iE sE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.lvOrbSlK)
      #[nE, wE, mE, nwE, c `S, c `SI, kSE, stepsE iE, mkApp (c `LR) iE, mulE sE (lit LCH), lit LCH])
    for i in [0:nb] do
      addThm (P ++ Name.mkSimple s!"lh{i}") (lhT (lit i)) reflBoolTrue
      for s in [0:NL] do
        addThm (P ++ Name.mkSimple s!"ls{i}_{s}") (lsT (lit i) (lit s)) reflBoolTrue
    let lhP := mkLambda `i .default natE (lhT (mkBVar 0))
    let hlhV := forallChain lhP nb fun i => mkConst (P ++ Name.mkSimple s!"lh{i}")
    let innerP := fun (iE : Expr) => mkLambda `s .default natE (lsT iE (mkBVar 0))
    let outerBody := fun (iE : Expr) =>
      mkForall `s .default natE (mkForall `h .default
        (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, lit NL])
        (lsT (iE.liftLooseBVars 0 2) (mkBVar 1)))
    let outerP := mkLambda `i .default natE (outerBody (mkBVar 0))
    let hlsV := forallChain outerP nb fun i =>
      forallChain (innerP (lit i)) NL fun s => mkConst (P ++ Name.mkSimple s!"ls{i}_{s}")
    let hoT := mkAppN (mkConst ``CFSG.KS.Raw.OrbsOK) #[nE, wE, c `S, c `SI, c `LR, kSE, nbE, c `BP, lit NL, lit LCH]
    let lhAll := mkForall `i .default natE (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, nbE]) (lhT (mkBVar 1)))
    let lsAll := mkForall `i .default natE (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, nbE]) (outerBody (mkBVar 1)))
    let hoV := mkAppN (mkConst ``And.intro) #[lhAll, lsAll, hlhV, hlsV]
    addThm (P ++ `ho) hoT hoV
    addDef (P ++ `NL) natE (lit NL)
