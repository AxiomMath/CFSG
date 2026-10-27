module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Std.Data.HashMap
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.GenSetReplay
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public import Certificates.Data.Kernel.SporSch.PairClT
public import Certificates.Kernel.SporSch.GenSetReplay

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen in
elab "#kss_cltdata " pre:ident nn:num ww:num nbb:num sId:ident bId:ident lvId:ident bsId:ident
    clId:ident hh:num rr:num bk:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let nb := nbb.getNat
  let H := hh.getNat
  let R := rr.getNat
  let B := bk.getNat
  let cn (s : Ident) := liftCoreM <| realizeGlobalConstNoOverload s
  let S ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) (← cn sId)
  let base ← liftTermElabM <| unsafe evalConst (Array Nat) (← cn bId)
  let levels ← liftTermElabM <| unsafe evalConst (Array CFSG.Monster.B.Co2.Native.Level) (← cn lvId)
  let bs ← liftTermElabM <| unsafe evalConst (List Nat) (← cn bsId)
  let cl ← liftTermElabM <| unsafe evalConst
    (List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat)) (← cn clId)
  let kS := S.size
  let Sinv := S.map (inv n)
  let NR := (n + 63) / 64
  let rowsOf := fun (fw : Nat) (a : Array Nat) => rows fw (a ++ Array.replicate (NR * 64 - a.size) 0)
  let lets := (Array.range nb).map fun i =>
    let idx := (Array.range kS).filter fun j => (List.range i).all fun t => (S[j]!)[base[t]!]! == base[t]!
    idx ++ idx.map (· + kS)
  let Ts := lets.map fun ls => Id.run do
    let mut T := ls.size
    for j in [0:ls.size] do
      T := T ||| (ls[j]! <<< (8 + 8 * j))
    return T
  let letA := fun (l : Nat) => if l < kS then S[l]! else Sinv[l - kS]!
  let LT := (Array.range (2 * kS)).foldl (fun acc l => acc ++ rowsOf w (letA l)) #[]
  let PT := (Array.range nb).foldl (fun acc i =>
    let L := levels[i]!
    acc ++ rowsOf 24 ((Array.range L.pts.size).map fun k =>
      L.par[k]! + ((lets[i]!)[L.lab[k]!]! <<< 16))) #[]
  let QT := (Array.range nb).foldl (fun acc i => acc ++ rowsOf w levels[i]!.pos) #[]
  let (_, elts, par, lab) := cl[0]!
  let c := elts.size
  let kg := 2
  let key := fun (nf : Array Nat) =>
    CFSG.Sporadic.Schreier.PairNative.imgKey n
      (CFSG.Sporadic.Schreier.PairNative.baseImgs bs (CFSG.Sporadic.Schreier.PairNative.nfWord levels nf))
  let keys := elts.map key
  let idx : Std.HashMap Nat Nat := (Array.range c).foldl (fun m i => m.insert keys[i]! i) {}
  let xs := (Array.range c).map fun i =>
    pack 16 elts[i]! ||| (par[i]! <<< (16 * nb)) ||| (lab[i]! <<< (16 * nb + 20))
  let gens := #[S[0]!, S[1]!]
  let gensInv := #[Sinv[0]!, Sinv[1]!]
  let ws := (Array.range c).map fun h => Id.run do
    let wd := CFSG.Sporadic.Schreier.PairNative.nfWord levels elts[h]!
    let mut v := 0
    for l in [0:kg] do
      let imgs := CFSG.Sporadic.Schreier.PairNative.conjImgs bs gens[l]! gensInv[l]! wd
      v := v ||| ((idx.getD (CFSG.Sporadic.Schreier.PairNative.imgKey n imgs) 0) <<< (20 * l))
    return v
  let before := Id.run do
    let mut out : Array Nat := #[]
    let mut k := 1
    for h in [0:c + 1] do
      while k < c && par[k]! < h do
        k := k + 1
      out := out.push k
    return out
  let nS := (c + H * R - 1) / (H * R)
  let nB := (c + B * R - 1) / (B * R)
  let C := (Array.range (nS * R + 1)).map fun q => if q * H < c then before[q * H]! else c
  let kw := (n ^ nb).log2 + 1
  let so := (Array.range c).qsort fun a b => keys[a]! < keys[b]!
  let soi := Id.run do
    let mut r := Array.replicate c 0
    for i in [0:c] do
      r := r.set! so[i]! i
    return r
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `Ts) Ts
    addTree (P ++ `LT) LT
    addTree (P ++ `PT) PT
    addTree (P ++ `QT) QT
    addTree (P ++ `XT) (rows (16 * nb + 28) xs)
    addTree (P ++ `WT) (rows (20 * kg) ws)
    addTree (P ++ `KT) (rows kw keys)
    addTree (P ++ `C) C
    addTree (P ++ `ST) (rows 20 so)
    addTree (P ++ `SIT) (rows 20 soi)
    addDef (P ++ `NR) natT (lit NR)
    addDef (P ++ `kw) natT (lit kw)
    addDef (P ++ `c) natT (lit c)
    addDef (P ++ `nS) natT (lit nS)
    addDef (P ++ `nB) natT (lit nB)

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen in
elab "#kss_b2 " pre:ident fId:ident g0:num g1:num rr:num : command => do
  let P := pre.getId
  let R := rr.getNat
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let s := fN.getString!
  let ty := fun (g r : Expr) => isTrue (mkApp2 (mkConst fN) g r)
  liftCoreM <| withOptions (Elab.async.set · false) do
    for g in [g0.getNat:g1.getNat] do
      for r in [0:R] do
        let nm := P ++ Name.mkSimple s!"{s}_{g}_{r}"
        CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty (lit g) (lit r), value := reflBoolTrue }
      let lamR := mkLambda `r .default natT (ty (lit g) (mkBVar 0))
      let vR := forallChain lamR R fun r => mkConst (P ++ Name.mkSimple s!"{s}_{g}_{r}")
      let nm := P ++ Name.mkSimple s!"{s}_{g}"
      let tyR := forallLt R fun r => ty (lit g) r
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := tyR, value := vR }

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen in
elab "#kss_b2all " pre:ident fId:ident gg:num rr:num : command => do
  let P := pre.getId
  let R := rr.getNat
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let s := fN.getString!
  let ty := fun (g r : Expr) => isTrue (mkApp2 (mkConst fN) g r)
  liftCoreM <| withOptions (Elab.async.set · false) do
    let lamG := mkLambda `g .default natT (forallLt R fun r => ty (mkBVar 2) r)
    let vG := forallChain lamG gg.getNat fun g => mkConst (P ++ Name.mkSimple s!"{s}_{g}")
    let nm := P ++ Name.mkSimple s!"{s}_all"
    let tyG := forallLt gg.getNat fun g => forallLt R fun r => ty (g.liftLooseBVars 0 2) r
    CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := tyG, value := vG }

end
