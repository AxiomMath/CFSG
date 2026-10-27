module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Std.Data.HashMap
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.GenSetReplay
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public import CFSG.Certificates.Kernel.SporSch.PairClSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound
public import Certificates.Kernel.SporSch.GenSetReplay

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen in
elab "#kss_nfclos " pre:ident pch:ident nn:num ww:num nbb:num lvId:ident bsId:ident gId:ident
    giId:ident clId:ident cc:num hh:num rr:num bk:num : command => do
  let P := pre.getId
  let Pch := pch.getId
  let n := nn.getNat
  let w := ww.getNat
  let nb := nbb.getNat
  let cap := cc.getNat
  let H := hh.getNat
  let R := rr.getNat
  let B := bk.getNat
  let cn (s : Ident) := liftCoreM <| realizeGlobalConstNoOverload s
  let lvN ← cn lvId
  let bsN ← cn bsId
  let gN ← cn gId
  let giN ← cn giId
  let clN ← cn clId
  let levels ← liftTermElabM <| unsafe evalConst (Array CFSG.Monster.B.Co2.Native.Level) lvN
  let bs ← liftTermElabM <| unsafe evalConst (List Nat) bsN
  let gens ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let gensInv ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) giN
  let cl ← liftTermElabM <| unsafe evalConst
    (List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat)) clN
  let _ := cap
  let kg := gens.size
  let key := fun (nf : Array Nat) =>
    CFSG.Sporadic.Schreier.PairNative.imgKey n
      (CFSG.Sporadic.Schreier.PairNative.baseImgs bs (CFSG.Sporadic.Schreier.PairNative.nfWord levels nf))
  let rx := 16 * nb + 28
  let rwW := 20 * kg
  let LRc := mkConst (Pch ++ `LR)
  let TRc := mkConst (Pch ++ `TR)
  let TRIc := mkConst (Pch ++ `TRI)
  let bsE := mkConst bsN
  let mut csE : Array Expr := #[]
  let mut allKeys : Array Nat := #[]
  let natE := natT
  let fnE := fnT
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `G) (gens.map (pack w))
    addTree (P ++ `GI) (gensInv.map (pack w))
  for j in [0:cl.length] do
    let (_, elts, par, lab) := cl[j]!
    let c := elts.size
    let idx : Std.HashMap Nat Nat := (Array.range c).foldl (fun m i => m.insert (key elts[i]!) i) {}
    let xs := (Array.range c).map fun i =>
      pack 16 elts[i]! ||| (par[i]! <<< (16 * nb)) ||| (lab[i]! <<< (16 * nb + 20))
    let ws := (Array.range c).map fun h => Id.run do
      let wd := CFSG.Sporadic.Schreier.PairNative.nfWord levels elts[h]!
      let mut v := 0
      for l in [0:kg] do
        let imgs := CFSG.Sporadic.Schreier.PairNative.conjImgs bs gens[l]! gensInv[l]! wd
        let k := CFSG.Sporadic.Schreier.PairNative.imgKey n imgs
        v := v ||| ((idx.getD k 0) <<< (20 * l))
      return v
    let before := Id.run do
      let mut out : Array Nat := #[]
      let mut k := 1
      for h in [0:c + 1] do
        while k < c && par[k]! < h do
          k := k + 1
        out := out.push k
      return out
    let curAt := fun (h : Nat) => before[h]!
    let nS := (c + H * R - 1) / (H * R)
    let nB := (c + B * R - 1) / (B * R)
    let C := (Array.range (nS * R + 1)).map fun q => if q * H < c then curAt (q * H) else c
    let sfx := toString j
    let XT := P ++ Name.mkSimple ("XT" ++ sfx)
    let WT := P ++ Name.mkSimple ("WT" ++ sfx)
    let Cn := P ++ Name.mkSimple ("C" ++ sfx)
    allKeys := allKeys ++ elts.map key
    liftCoreM <| withOptions (Elab.async.set · false) do
      addTree XT (rows rx xs)
      addTree WT (rows rwW ws)
      addTree Cn C
      addDef (P ++ Name.mkSimple ("c" ++ sfx)) natE (lit c)
      addDef (P ++ Name.mkSimple ("nS" ++ sfx)) natE (lit nS)
      addDef (P ++ Name.mkSimple ("nB" ++ sfx)) natE (lit nB)
      let X := app ``CFSG.KS.SporSch.rowGet #[mkConst XT, lit rx]
      let W := app ``CFSG.KS.SporSch.rowGet #[mkConst WT, lit rwW]
      let Cf := mkConst Cn
      let runT := fun (q : Expr) => isTrue (mkApp2 (mkConst ``Nat.beq)
        (app ``CFSG.KS.SporSch.runNF #[lit n, lit w, LRc, TRc, TRIc, lit nb, bsE, mkConst (P ++ `G),
          mkConst (P ++ `GI), X, W, lit kg, lit c, lit H, mkApp2 (mkConst ``Nat.mul) q (lit H), mkApp Cf q])
        (mkApp Cf (mkApp (mkConst ``Nat.succ) q)))
      addChain2 P ("run" ++ sfx) ("hrun" ++ sfx) nS R runT
      let nfT := fun (q : Expr) => isTrue (app ``CFSG.KC.Enum.allBlk
        #[mkApp2 (mkConst ``Nat.mul) q (lit B), app ``CFSG.KS.SporSch.nfOKAt #[lit n, lit w, LRc, lit nb, X, lit c],
          lit B])
      addChain2 P ("nfok" ++ sfx) ("hnf" ++ sfx) nB R nfT
    let K := app ``CFSG.KS.SporSch.nfKeyX #[lit n, lit w, LRc, TRc, lit nb, bsE, mkConst XT, lit rx]
    csE := csE.push (mkApp4 (mkConst ``Prod.mk [0, 0]) natE fnE (lit c) K)
  let N := allKeys.size
  let so := (Array.range N).qsort fun a b => allKeys[a]! < allKeys[b]!
  let soi := Id.run do
    let mut r := Array.replicate N 0
    for i in [0:N] do
      r := r.set! so[i]! i
    return r
  let pty := mkApp2 (mkConst ``Prod [0, 0]) natE fnE
  let csL := csE.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) pty x acc) (mkApp (mkConst ``List.nil [0]) pty)
  let nB := (N + B * R - 1) / (B * R)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `cs) (mkApp (mkConst ``List [0]) pty) csL
    addTree (P ++ `ST) (rows 20 so)
    addTree (P ++ `SIT) (rows 20 soi)
    addDef (P ++ `N) natE (lit N)
    addDef (P ++ `nBs) natE (lit nB)
    let SO := app ``CFSG.KS.SporSch.rowGet #[mkConst (P ++ `ST), lit 20]
    let SOI := app ``CFSG.KS.SporSch.rowGet #[mkConst (P ++ `SIT), lit 20]
    let srtT := fun (q : Expr) => isTrue (app ``CFSG.KC.Enum.allBlk
      #[mkApp2 (mkConst ``Nat.mul) q (lit B), app ``CFSG.KS.SporSch.keySortAt #[mkConst (P ++ `cs), SO, SOI, lit N],
        lit B])
    addChain2 P "srt" "hsrt" nB R srtT

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen in
elab "#kss_cnt3 " pre:ident pch:ident nn:num ww:num lvId:ident bsId:ident mm:num xsId:ident
    rpId:ident cdId:ident : command => do
  let P := pre.getId
  let Pch := pch.getId
  let n := nn.getNat
  let w := ww.getNat
  let m := mm.getNat
  let cn (s : Ident) := liftCoreM <| realizeGlobalConstNoOverload s
  let lvN ← cn lvId
  let bsN ← cn bsId
  let xsN ← cn xsId
  let rpN ← cn rpId
  let cdN ← cn cdId
  let levels ← liftTermElabM <| unsafe evalConst (Array CFSG.Monster.B.Co2.Native.Level) lvN
  let bs ← liftTermElabM <| unsafe evalConst (List Nat) bsN
  let xs ← liftTermElabM <| unsafe evalConst (List (Array Nat)) xsN
  let conds ← liftTermElabM <| unsafe evalConst (List (List Bool × Nat)) cdN
  let L0 := levels[0]!
  let L1 := levels[1]!
  let L2 := levels[2]!
  let cs := (Array.range L0.pts.size).map fun k0 => Id.run do
    let t0 := L0.tr[k0]!
    let mut a := 0
    let mut b := 0
    for k1 in [0:L1.pts.size] do
      for k2 in [0:L2.pts.size] do
        let y := [L2.tr[k2]!, L1.tr[k1]!, t0]
        if CFSG.Sporadic.Schreier.PairNative.ordB bs y m then
          a := a + 1
          if CFSG.Sporadic.Schreier.PairNative.condsOK bs xs y conds then
            b := b + 1
    return a + (b <<< 20)
  let _ := n
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `CS) cs
    let ty := fun (q : Expr) => mkApp3 (mkConst ``Eq [1]) natT
      (app ``CFSG.KS.SporSch.cnt3 #[lit n, lit w, mkConst (Pch ++ `LR), mkConst (Pch ++ `TR),
        mkConst bsN, lit m, mkConst rpN, mkConst cdN, q])
      (mkApp (mkConst (P ++ `CS)) q)
    for q in [0:cs.size] do
      let nm := P ++ Name.mkSimple ("k" ++ toString q)
      let tq := ty (lit q)
      let pf := mkApp2 (mkConst ``Eq.refl [1]) natT (mkApp (mkConst (P ++ `CS)) (lit q))
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := tq, value := pf }
    let lam := mkLambda `q .default natT (ty (mkBVar 0))
    let v := forallChain lam cs.size fun q => mkConst (P ++ Name.mkSimple ("k" ++ toString q))
    let tyAll := forallLt cs.size ty
    CFSG.KC.addThmDecl <| { name := P ++ `hk, levelParams := [], type := tyAll, value := v }
    addDef (P ++ `c0) natT (lit cs.size)

end
