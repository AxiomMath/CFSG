module

public import CFSG.Certificates.Kernel.SporSch.TitsEnum5Sound
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Sporadic.Schreier.TitsChain
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kst_all5 " pre:ident nn:num ww:num a0:num a1:num lrId:ident trId:ident qId:ident :
    command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let c0 := a0.getNat
  let c1 := a1.getNat
  let lrN ← liftCoreM <| realizeGlobalConstNoOverload lrId
  let trN ← liftCoreM <| realizeGlobalConstNoOverload trId
  let qN ← liftCoreM <| realizeGlobalConstNoOverload qId
  let nE := lit n
  let nwE := mulE nE (lit w)
  let LR := mkConst lrN
  let TR := mkConst trN
  let Q := mkConst qN
  let natE := natT
  let ltE := fun (x b : Expr) => mkAppN (mkConst ``LT.lt [0]) #[natE, mkConst ``instLTNat, x, b]
  let sT := fun (aE bE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.e5ab)
    #[nE, nwE, LR, TR, Q, aE, bE])
  let rc := fun (i : Nat) => mkApp (mkConst ``CFSG.KS.Raw.rcnt) (mkApp LR (lit i))
  let beqT := fun (i c : Nat) => isTrue (mkApp2 (mkConst ``Nat.beq) (rc i) (lit c))
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KC.addThmDecl <| { name := P ++ `c0, levelParams := [], type := beqT 0 c0, value := reflBoolTrue }
    CFSG.KC.addThmDecl <| { name := P ++ `c1, levelParams := [], type := beqT 1 c1, value := reflBoolTrue }
    for a in [0:c0] do
      for b in [0:c1] do
        let nm := P ++ Name.mkSimple s!"s{a}_{b}"
        let ty := sT (lit a) (lit b)
        CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := reflBoolTrue }
    let innerP := fun (aE : Expr) => mkLambda `b .default natE (sT aE (mkBVar 0))
    let outerBody := fun (aE : Expr) =>
      mkForall `b .default natE (mkForall `h .default (ltE (mkBVar 0) (lit c1))
        (sT (aE.liftLooseBVars 0 2) (mkBVar 1)))
    let outerP := mkLambda `a .default natE (outerBody (mkBVar 0))
    let hV := forallChain outerP c0 fun a =>
      forallChain (innerP (lit a)) c1 fun b => mkConst (P ++ Name.mkSimple s!"s{a}_{b}")
    let eq0 := mkAppN (mkConst ``Nat.eq_of_beq_eq_true) #[rc 0, lit c0, mkConst (P ++ `c0)]
    let eq1 := mkAppN (mkConst ``Nat.eq_of_beq_eq_true) #[rc 1, lit c1, mkConst (P ++ `c1)]
    let allT := isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.all5K) #[nE, nwE, LR, TR, Q])
    let allV := mkAppN (mkConst ``CFSG.KS.SporSch.all5K_of)
      #[nE, nwE, lit c0, lit c1, LR, TR, Q, eq0, eq1, hV]
    CFSG.KC.addThmDecl <| { name := P ++ `all, levelParams := [], type := allT, value := allV }
