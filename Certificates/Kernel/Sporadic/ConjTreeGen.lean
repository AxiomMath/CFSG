module

public import Certificates.Data.Kernel.Spor.ConjTree
public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

namespace CFSG.KS.ConjTreeGen

meta def addThm (nm : Name) (ty : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := reflBoolTrue }

meta def addThmV (nm : Name) (ty v : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := v }

end CFSG.KS.ConjTreeGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.ConjTreeGen in
elab "#ks_conjtree " pre:ident nn:num ww:num rr:num ch:num gId:ident s0Id:ident tId:ident
    gsId:ident gsiId:ident tfId:ident wtN:num paId:ident wpN:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let r := rr.getNat
  let CH := ch.getNat
  let wt := wtN.getNat
  let wp := wpN.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let s0N ← liftCoreM <| realizeGlobalConstNoOverload s0Id
  let tN ← liftCoreM <| realizeGlobalConstNoOverload tId
  let gsN ← liftCoreM <| realizeGlobalConstNoOverload gsId
  let gsiN ← liftCoreM <| realizeGlobalConstNoOverload gsiId
  let tfN ← liftCoreM <| realizeGlobalConstNoOverload tfId
  let paN ← liftCoreM <| realizeGlobalConstNoOverload paId
  let G ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let s0 ← liftTermElabM <| unsafe evalConst (Array Nat) s0N
  let tree ← liftTermElabM <| unsafe evalConst (Array Nat) tN
  let Gi := G.map (inv n)
  let mut T : Array (Array Nat) := #[s0]
  for t in tree do
    let g := G[t % r]!
    T := T.push (comp n g (comp n T[t / r]! Gi[t % r]!))
  let N := tree.size
  let m := T.size
  let NS1 := (N + CH - 1) / CH
  let NS2 := (m + CH - 1) / CH
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `T) (T.map (pack w))
    let nE := lit n
    let wE := lit w
    let rE := lit r
    let natE := natT
    let c := fun (s : Name) => mkConst (P ++ s)
    let stP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.ConjTree.stepSl)
      #[nE, wE, rE, mkConst gsN, mkConst gsiN, c `T, mkConst tfN, lit wt, lit N,
        mulE (mkBVar 0) (lit CH), lit CH]))
    let acP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.ConjTree.actSl)
      #[nE, wE, rE, mkConst gsN, mkConst gsiN, c `T, mkConst paN, lit wp, lit m,
        mulE (mkBVar 0) (lit CH), lit CH]))
    let diP := mkLambda `s .default natE (isTrue (mkAppN (mkConst ``CFSG.KS.ConjTree.distSl)
      #[c `T, lit m, mulE (mkBVar 0) (lit CH), lit CH]))
    for s in [0:NS1] do
      addThm (P ++ Name.mkSimple s!"st{s}") (mkApp stP (lit s)).headBeta
    for s in [0:NS2] do
      addThm (P ++ Name.mkSimple s!"ac{s}") (mkApp acP (lit s)).headBeta
      addThm (P ++ Name.mkSimple s!"di{s}") (mkApp diP (lit s)).headBeta
    let ltE := fun (a b : Expr) => mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, a, b]
    let allT := fun (Pl : Expr) (k : Nat) => mkForall `s .default natE (mkForall `h .default
      (ltE (mkBVar 0) (lit k)) (mkApp Pl (mkBVar 1)).headBeta)
    addThmV (P ++ `hS) (allT stP NS1)
      (forallChain stP NS1 fun s => mkConst (P ++ Name.mkSimple s!"st{s}"))
    addThmV (P ++ `hA) (allT acP NS2)
      (forallChain acP NS2 fun s => mkConst (P ++ Name.mkSimple s!"ac{s}"))
    addThmV (P ++ `hD) (allT diP NS2)
      (forallChain diP NS2 fun s => mkConst (P ++ Name.mkSimple s!"di{s}"))
