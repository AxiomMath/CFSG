module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Std.Data.HashMap
public meta import Certificates.Kernel.SporSch.Ly.GenLy
public meta import Certificates.Kernel.SporSch.Ly.GenSyl
public meta import Certificates.Kernel.SporSch.GenSetReplay
public meta import CFSG.Sporadic.Schreier.LyCheckSeven
public import Certificates.Kernel.SporSch.Ly.GenSyl
public import Lean.Message

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.LySevGen

open CFSG.KC.Tab CFSG.KS.SporSch.LySylGen

meta def natArrE (a : Array Nat) : Expr := mkApp2 (mkConst ``List.toArray [0]) natT (natListE a.toList)

meta def arrArrE (as : Array (Array Nat)) : Expr :=
  let aT := mkApp (mkConst ``Array [0]) natT
  mkApp2 (mkConst ``List.toArray [0]) aT
    (as.foldr (fun a acc => mkApp3 (mkConst ``List.cons [0]) aT (natArrE a) acc)
      (mkApp (mkConst ``List.nil [0]) aT))

meta def pairArrE (ps : Array (Array Nat × Array Nat)) : Expr :=
  let aT := mkApp (mkConst ``Array [0]) natT
  let pT := mkApp2 (mkConst ``Prod [0, 0]) aT aT
  mkApp2 (mkConst ``List.toArray [0]) pT
    (ps.foldr (fun p acc => mkApp3 (mkConst ``List.cons [0]) pT
      (mkApp4 (mkConst ``Prod.mk [0, 0]) aT aT (natArrE p.1) (natArrE p.2)) acc)
      (mkApp (mkConst ``List.nil [0]) pT))

meta def pack3 (a : Array Nat) : Nat := Id.run do
  let mut acc := 0
  for t in [0:a.size] do
    acc := acc ||| ((a[t]! % 8) <<< (3 * t))
  return acc

meta def srows (rw : Nat) (vs : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut i := 0
  while i < vs.size do
    let salt := ((i / 64 + 1) * 11400714819323198485) % 18446744073709551616
    let mut acc := salt
    for j in [0:64] do
      if i + j < vs.size then
        acc := acc ||| (vs[i + j]! <<< (64 + rw * j))
    out := out.push acc
    i := i + 64
  return out

end CFSG.KS.SporSch.LySevGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.LyGen CFSG.KS.SporSch.LySylGen in
open CFSG.KS.SporSch.LySevGen in
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native in
elab "#kly_sev " pre:ident : command => do
  let P := pre.getId
  let b4 := powM 5 111 (matB ()) 4
  let as := aStarArr b4
  let ls := (strongWordsTxt.splitOn "\n").dropLast.map parseInts
  let padUp : Array (Array Nat) := Array.ofFn (n := 111) fun i => Array.ofFn (n := 111) fun j =>
    if j.val < 7 then (uArr[i.val]!)[j.val]! else 0
  let dg := (List.range bpRootArr.size).foldl (fun acc i => acc ||| (bpRootArr[i]! <<< (4 * i))) 0
  let ra := (Array.range 5).map fun j => restrArr (pairAt as (j + 2)).1
  let gens := fun j => restrArr (pairAt as (j + 2)).1
  let vals := dagArr gens
  let hp := hGenPairs as
  let v := evalWordM seedM (seedMInv b4) (transporterWord ())
  let vi := invM 5 111 v
  let t := mulM 5 111 (mulM 5 111 vi matA) v
  let llT := mkApp (mkConst ``List [0]) (mkApp (mkConst ``List [0]) (mkConst ``Int))
  let intLT := mkApp (mkConst ``List [0]) (mkConst ``Int)
  let lsE := ls.foldr (fun l acc => mkApp3 (mkConst ``List.cons [0]) intLT (intListE l) acc)
    (mkApp (mkConst ``List.nil [0]) intLT)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `AF) (as.map fun p => packM p.1)
    addTree (P ++ `AI) (as.map fun p => packM p.2)
    addDef (P ++ `nAS) natT (lit as.size)
    addDef (P ++ `LS) llT lsE
    for j in [2:7] do
      addDef (P ++ Name.mkSimple s!"SW{j}") intLT (intListE (ls.getD j []))
    addDef (P ++ `UP) natT (lit (packM padUp))
    addDef (P ++ `DG) natT (lit dg)
    addDef (P ++ `nDG) natT (lit bpRootArr.size)
    addDef (P ++ `RA) (mkApp (mkConst ``Array [0]) (mkApp (mkConst ``Array [0]) natT)) (arrArrE ra)
    addDef (P ++ `VALS) (mkApp (mkConst ``Array [0]) (mkApp (mkConst ``Array [0]) natT))
      (arrArrE vals)
    let aT := mkApp (mkConst ``Array [0]) natT
    addDef (P ++ `HP) (mkApp (mkConst ``Array [0]) (mkApp2 (mkConst ``Prod [0, 0]) aT aT))
      (pairArrE hp)
    addDef (P ++ `V) natT (lit (packM v))
    addDef (P ++ `VI) natT (lit (packM vi))
    addDef (P ++ `TT) natT (lit (packM t))
    addDef (P ++ `RT) aT (natArrE (restrArr t))

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.LyGen in
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native in
elab "#kly_sevchain " pre:ident jj:num cc:num : command => do
  let P := pre.getId
  let j := jj.getNat
  let c := cc.getNat
  let b4 := powM 5 111 (matB ()) 4
  let as := aStarArr b4
  let word := (strongWordsTail).getD (j - 2) []
  let g := fun (k : Nat) => if k < j then (pairAt as k).1 else idM 111
  let gi := fun (k : Nat) => if k < j then (pairAt as k).2 else idM 111
  let m := (word.length + c - 1) / c
  let mut X := idM 111
  let mut ks : Array Nat := #[packM X]
  for k in [0:m] do
    X := wordFromM g gi X ((word.drop (k * c)).take c)
    ks := ks.push (packM X)
  let K := P ++ Name.mkSimple s!"K{j}"
  let cst := fun (nm : Name) => mkConst nm
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree K ks
    addDef (K ++ `m) natT (lit m)
    let ty := fun (k : Expr) => isTrue (mkApp2 (mkConst ``Nat.beq)
      (mkAppN (mkConst ``CFSG.KS.SporSch.LyM.wordR) #[lit 5, lit 12, lit 1332, lit 111, lit 8,
        cst `CFSG.KD.OrdLy.L, cst `CFSG.KD.OrdLy.H, cst `CFSG.KD.OrdLy.CM, cst `CFSG.KD.OrdLy.RM,
        mkApp (cst (P ++ `AFx)) (lit j), mkApp (cst (P ++ `AIx)) (lit j), mkApp (cst K) k,
        mkApp3 (mkConst ``List.take [0]) (mkConst ``Int) (lit c)
          (mkApp3 (mkConst ``List.drop [0]) (mkConst ``Int) (mkApp2 (mkConst ``Nat.mul) k (lit c))
            (cst (P ++ Name.mkSimple s!"SW{j}")))])
      (mkApp (cst K) (mkApp (mkConst ``Nat.succ) k)))
    for k in [0:m] do
      let nmk := K ++ Name.mkSimple s!"c{k}"
      CFSG.KC.addThmDecl <| { name := nmk, levelParams := [], type := ty (lit k), value := reflBoolTrue }
    let lam := mkLambda `k .default natT (ty (mkBVar 0))
    let v := forallChain lam m fun k => mkConst (K ++ Name.mkSimple s!"c{k}")
    CFSG.KC.addThmDecl <| { name := K ++ `all, levelParams := [], type := forallLtE m ty, value := v }

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.LyGen CFSG.KS.SporSchGen in
open CFSG.KS.SporSch.LySevGen in
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native in
elab "#kly_sevvec " pre:ident ii:num hh:num : command => do
  let P := pre.getId
  let i := ii.getNat
  let Hh := hh.getNat
  let b4 := powM 5 111 (matB ()) 4
  let as := aStarArr b4
  let vals := dagArr fun j => restrArr (pairAt as (j + 2)).1
  let gens := ((hLevelGens.getD i []).map fun k => vals.getD k (id7 ())).toArray
  let (pts, par, lab) := vecBFS (stdVec i) gens
  let c := pts.size
  let E := pts.map pack3
  let PL := (Array.range c).map fun k => par[k]! + (lab[k]! <<< 20)
  let code := fun (v : Array Nat) => (List.range 7).foldl (fun acc r => acc + v[r]! * 5 ^ r) 0
  let nS := (c + Hh - 1) / Hh
  let mut cnt := 1
  let mut M : Nat := 1 <<< code pts[0]!
  let mut sts : Array Nat := #[cnt + (M <<< 20)]
  for q in [0:nS] do
    for h in [q * Hh:(q + 1) * Hh] do
      if h < cnt then
        for j in [0:gens.size] do
          let y := mv7 gens[j]! pts[h]!
          let k := code y
          if (M >>> k) % 2 == 0 then
            cnt := cnt + 1
            M := M ||| (1 <<< k)
    sts := sts.push (cnt + (M <<< 20))
  let s := toString i
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ Name.mkSimple s!"GP{s}") (gens.map pack3)
    addTree (P ++ Name.mkSimple s!"ET{s}") (srows 21 E)
    addTree (P ++ Name.mkSimple s!"PT{s}") (srows 24 PL)
    addTree (P ++ Name.mkSimple s!"C{s}") sts
    addDef (P ++ Name.mkSimple s!"c{s}") natT (lit c)
    addDef (P ++ Name.mkSimple s!"nS{s}") natT (lit nS)
    addDef (P ++ Name.mkSimple s!"kg{s}") natT (lit gens.size)

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.LyGen CFSG.KS.SporSchGen in
open CFSG.KS.SporSch.LySevGen in
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native in
elab "#kly_sevconj " pre:ident hh:num : command => do
  let P := pre.getId
  let Hh := hh.getNat
  let b4 := powM 5 111 (matB ()) 4
  let as := aStarArr b4
  let hp := hGenPairs as
  let v := evalWordM seedM (seedMInv b4) (transporterWord ())
  let vi := invM 5 111 v
  let rt := restrArr (mulM 5 111 (mulM 5 111 vi matA) v)
  let kg := hp.size
  let KC : Array Nat := (Array.range 49).map fun t => Id.run do
    let mut acc := 0
    for j in [0:kg] do
      for s in [0:49] do
        let e := (hp[j]!.1)[7 * (s / 7) + t / 7]! * (hp[j]!.2)[7 * (t % 7) + s % 7]! % 5
        acc := acc ||| (e <<< (980 * j + 20 * s))
    return acc
  let QM := (List.range (49 * kg)).foldl (fun acc s => acc ||| (255 <<< (20 * s))) 0
  let imgs := fun (x : Nat) =>
    let Y := (List.range 49).foldl (fun acc t => acc + ((x >>> (3 * t)) &&& 7) * KC[t]!) 0
    Y - 5 * (((Y * 205) >>> 10) &&& QM)
  let comp := fun (Y j : Nat) => (List.range 49).foldl (fun acc t =>
    acc ||| (((Y >>> (980 * j + 20 * t)) &&& 7) <<< (3 * t))) 0
  let root := pack3 rt
  let mut pts : Array Nat := #[root]
  let mut index : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert root 0
  let mut PL : Array Nat := #[0]
  let mut WS : Array Nat := #[]
  let cap := 406875
  for h in [0:cap] do
    if h < pts.size then
      let Y := imgs pts[h]!
      let mut wh := 0
      for j in [0:kg] do
        let y := comp Y j
        match index[y]? with
        | some k => wh := wh ||| (k <<< (19 * j))
        | none =>
          wh := wh ||| (pts.size <<< (19 * j))
          index := index.insert y pts.size
          pts := pts.push y
          PL := PL.push (h + (j <<< 19))
      WS := WS.push wh
  let c := pts.size
  let so := ((Array.range c).qsort fun a b => pts[a]! < pts[b]!)
  let mut soi : Array Nat := Array.replicate c 0
  for k in [0:c] do
    soi := soi.set! so[k]! k
  let nS := (c + Hh - 1) / Hh
  let mut cnts : Array Nat := #[1]
  let mut cnt := 1
  for q in [0:nS] do
    for h in [q * Hh:(q + 1) * Hh] do
      if h < c then
        for j in [0:kg] do
          if (WS[h]! >>> (19 * j)) % 524288 == cnt then cnt := cnt + 1
    cnts := cnts.push cnt
  logInfo m!"conjugate orbit: {c} entries, {WS.size} heads, {nS} slices"
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `KC) KC
    addDef (P ++ `QM) natT (lit QM)
    addTree (P ++ `ET) (srows 147 pts)
    addTree (P ++ `WT) (srows 95 WS)
    addTree (P ++ `PT) (srows 24 PL)
    addTree (P ++ `SO) (srows 20 so)
    addTree (P ++ `SOI) (srows 20 soi)
    addTree (P ++ `C) cnts
    addDef (P ++ `c) natT (lit c)
    addDef (P ++ `nS) natT (lit nS)

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen in
elab "#kly_chainR " pre:ident nmI:ident qId:ident g0:num g1:num rr:num : command => do
  let P := pre.getId
  let qN ← liftCoreM <| realizeGlobalConstNoOverload qId
  let nm := nmI.getId.toString
  let R := rr.getNat
  let ty := fun q => isTrue (mkApp (mkConst qN) q)
  liftCoreM <| withOptions (Elab.async.set · false) do
    for g in [g0.getNat:g1.getNat] do
      for r in [0:R] do
        let nmq := P ++ Name.mkSimple s!"{nm}_{g}_{r}"
        let tyq := ty (idxE (lit g) R (lit r))
        CFSG.KC.addThmDecl <| { name := nmq, levelParams := [], type := tyq, value := reflBoolTrue }
      let lamR := mkLambda `r .default natT (ty (idxE (lit g) R (mkBVar 0)))
      let vR := forallChain lamR R fun r => mkConst (P ++ Name.mkSimple s!"{nm}_{g}_{r}")
      let nmg := P ++ Name.mkSimple s!"{nm}_{g}"
      let tyR := forallLt R fun r => ty (idxE (lit g) R r)
      CFSG.KC.addThmDecl <| { name := nmg, levelParams := [], type := tyR, value := vR }

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen in
elab "#kly_chainJoin " pre:ident nmI:ident qId:ident ng:num rr:num : command => do
  let P := pre.getId
  let qN ← liftCoreM <| realizeGlobalConstNoOverload qId
  let nm := nmI.getId.toString
  let R := rr.getNat
  let ty := fun q => isTrue (mkApp (mkConst qN) q)
  liftCoreM <| withOptions (Elab.async.set · false) do
    let lamG := mkLambda `g .default natT (forallLt R fun r => ty (idxE (mkBVar 2) R r))
    let vG := forallChain lamG ng.getNat fun g => mkConst (P ++ Name.mkSimple s!"{nm}_{g}")
    let nmAll := P ++ Name.mkSimple s!"{nm}All"
    let tyG := forallLt ng.getNat fun g => forallLt R fun r => ty (idxE (g.liftLooseBVars 0 2) R r)
    CFSG.KC.addThmDecl <| { name := nmAll, levelParams := [], type := tyG, value := vG }

end
