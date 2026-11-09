module

public import Certificates.Kernel.Sporadic.RawGenSplitP
public import CFSG.Certificates.Kernel.Spor.SchBlocks
public meta import Certificates.Kernel.Sporadic.RawGenSplit
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KS.RawGen

open CFSG.KC.Tab

meta def addSchBlocks (nm : Name) (args : Array Expr) (h0 : Expr) (CH u : Nat) (ty : Expr) :
    CoreM Unit := do
  let q := (CH + u - 1) / u
  let piece := fun (d : Nat) => Name.mkStr nm.getPrefix s!"{nm.getString!}_{d}"
  let uP := mkLambda `d .default natT (isTrue (mkAppN (mkConst `CFSG.KS.Raw.schK)
    (args ++ #[mkApp2 (mkConst ``Nat.add) h0 (mkApp2 (mkConst ``Nat.mul) (lit u) (mkBVar 0)),
      lit u])))
  for d in [0:q] do
    addThm (piece d) (mkApp uP (lit d)).headBeta reflBoolTrue
  let rB := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let hu := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (lit 1) (lit u) rB
  let hc := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (lit CH) (mulE (lit q) (lit u)) rB
  addThm nm ty (mkAppN (mkConst `CFSG.KS.Raw.schK_of_blocks)
    (args ++ #[h0, lit CH, lit u, lit q, hu, hc, forallChain uP q fun d => mkConst (piece d)]))

end CFSG.KS.RawGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.RawGenSplit in
elab "#ks_rawchain_sl2_schb " pre:ident ii:num lo:num hi:num uu:num : command => do
  let P := pre.getId
  let c ← ctxOf P
  let CH ← natOf (P ++ `pCH)
  let i := ii.getNat
  let iE := lit i
  let args := #[c.nE, c.wE, c.mE, c.nwE, c.idE, c.k `S, c.k `SI, c.k `LR, c.k `TR, c.k `TRI,
    lit c.kS, c.k `BP, lit c.nb, iE, c.steps iE]
  withSync do
    for s in [lo.getNat:hi.getNat] do
      addSchBlocks (P ++ Name.mkSimple s!"sch{i}_{s}") args (mulE (lit s) (lit CH)) CH uu.getNat
        (schT c CH iE (lit s))


open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#ks_rawchain_schb " pre:ident nn:num ww:num ch:num kk:num bb:num uu:num :
    command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let CH := ch.getNat
  let u := uu.getNat
  let kS := kk.getNat
  let nb := bb.getNat
  let NS := (n + CH - 1) / CH
  let natE := natT
  liftCoreM <| withOptions (Elab.async.set · false) do
    let nE := lit n
    let wE := lit w
    let mE := mkApp (mkConst ``CFSG.KS.mask) wE
    let nwE := mulE nE wE
    let idE := mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE
    let c := fun (s : Name) => mkConst (P ++ s)
    let kSE := lit kS
    let nbE := lit nb
    let stepsE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KS.Raw.stepsAt) #[nE, wE, c `S, kSE, c `BP, iE]
    let schT := fun (iE sE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.schK)
      #[nE, wE, mE, nwE, idE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, c `BP, nbE, iE, stepsE iE,
        mulE sE (lit CH), lit CH])
    for i in [0:nb] do
      for s in [0:NS] do
        addSchBlocks (P ++ Name.mkSimple s!"sch{i}_{s}")
          #[nE, wE, mE, nwE, idE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, c `BP, nbE, lit i,
            stepsE (lit i)] (mulE (lit s) (lit CH)) CH u (schT (lit i) (lit s))
    let innerP := fun (iE : Expr) => mkLambda `s .default natE (schT iE (mkBVar 0))
    let outerBody := fun (iE : Expr) =>
      mkForall `s .default natE (mkForall `h .default
        (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, lit NS])
        (schT (iE.liftLooseBVars 0 2) (mkBVar 1)))
    let outerP := mkLambda `i .default natE (outerBody (mkBVar 0))
    let hsV := forallChain outerP nb fun i =>
      forallChain (innerP (lit i)) NS fun s => mkConst (P ++ Name.mkSimple s!"sch{i}_{s}")
    let hsT := mkForall `i .default natE (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, mkBVar 0, nbE])
      (outerBody (mkBVar 1)))
    addThm (P ++ `hs) hsT hsV
    addDef (P ++ `NS) natE (lit NS)

end
