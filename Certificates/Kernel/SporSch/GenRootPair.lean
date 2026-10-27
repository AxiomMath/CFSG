module

public import Certificates.Data.Kernel.SporSch.RootPair
public import CFSG.Certificates.Kernel.Spor.RawSound
public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Kernel.SporSch.J1.GenPt
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Kernel.SporSch.J1.GenPt

open Lean Elab Command

public section

namespace CFSG.KS.SporSch.RPG

open CFSG.KC.Tab

meta def listIntT : Expr := mkApp (mkConst ``List [0]) (mkConst ``Int)

meta def intE (z : Int) : Expr :=
  if 0 ≤ z then mkApp (mkConst ``Int.ofNat) (lit z.toNat)
  else mkApp (mkConst ``Int.negSucc) (lit ((-z).toNat - 1))

meta def listIntE (l : List Int) : Expr :=
  l.foldr (fun z acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Int) (intE z) acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Int))

meta def listListIntE (l : List (List Int)) : Expr :=
  l.foldr (fun w acc => mkApp3 (mkConst ``List.cons [0]) listIntT (listIntE w) acc)
    (mkApp (mkConst ``List.nil [0]) listIntT)

meta def evalLLI (id : Ident) : CommandElabM (List (List Int)) := do
  let nm ← liftCoreM <| realizeGlobalConstNoOverload id
  liftTermElabM <| unsafe evalConst (List (List Int)) nm

meta def evalLLLI (id : Ident) : CommandElabM (List (List (List Int))) := do
  let nm ← liftCoreM <| realizeGlobalConstNoOverload id
  liftTermElabM <| unsafe evalConst (List (List (List Int))) nm

end CFSG.KS.SporSch.RPG

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.JPG CFSG.KS.SporSch.RPG in
elab "#kss_rootpair " pre:ident nn:num ww:num sId:ident bId:ident ngN:num zId:ident
    gId:ident rwId:ident uwId:ident jwId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let ng := ngN.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let Zarr ← evalArr zId
  let GA ← evalArrs gId
  let RW ← evalLLI rwId
  let UW ← evalLLLI uwId
  let JW ← evalLLLI jwId
  let L := levelsOf n S base
  let N := L.foldl (fun a T => a * T.size) 1
  let G := (S.toList.take ng).toArray
  let GI := G.map invA
  let els := (Array.range N).map fun j => elemOf L n j
  let isO := els.map fun x => orderA x == 2
  let mut cls : Array Nat := Array.replicate N N
  let mut ncl := 0
  let mut minIdx : Array Nat := #[]
  for j0 in [0:N] do
    if isO[j0]! && cls[j0]! == N then
      cls := cls.set! j0 ncl
      minIdx := minIdx.push j0
      let mut bl : Array Nat := #[j0]
      let mut h := 0
      while h < bl.size do
        let x := els[bl[h]!]!
        for l in [0:ng] do
          let jz := indexOf L base (comp G[l]! (comp x GI[l]!))
          if cls[jz]! == N then
            cls := cls.set! jz ncl
            bl := bl.push jz
        h := h + 1
      ncl := ncl + 1
  let mut O : Array Nat := #[0]
  let mut posOf : Array Nat := Array.replicate N 0
  let mut cnt := 0
  for ci in [0:ncl] do
    for j in [0:N] do
      if cls[j]! == ci then
        posOf := posOf.set! j cnt
        cnt := cnt + 1
    O := O.push cnt
  let _ := O
  let zj := indexOf L base Zarr
  if els[zj]! != Zarr then throwError "#kss_rootpair: Z is not in the group"
  let zc := cls[zj]!
  let mut repOf : Array Nat := Array.replicate ncl N
  let mut wOf : Array Nat := Array.replicate ncl RW.length
  repOf := repOf.set! zc zj
  for k in [0:RW.length] do
    let g := evalW n G RW[k]!
    let j := indexOf L base g
    if els[j]! != g then throwError "#kss_rootpair: representative {k} is not in the group"
    let ci := cls[j]!
    if ci == N then throwError "#kss_rootpair: representative {k} is not of order 2"
    if repOf[ci]! != N then throwError "#kss_rootpair: two representatives of class {ci}"
    repOf := repOf.set! ci j
    wOf := wOf.set! ci k
  if repOf.any (· == N) then throwError "#kss_rootpair: a class without representative"
  let nG := GA[0]!.size
  let _ := nG
  let mut XW : Array (List Int) := #[]
  let mut UO : Array Nat := #[0]
  let mut CU : Array Nat := #[]
  let mut JO : Array Nat := #[0]
  let mut CJ : Array Nat := #[]
  for ci in [0:ncl] do
    let k := wOf[ci]!
    for wd in UW.getD k [] do
      CU := CU.push XW.size
      XW := XW.push wd
    UO := UO.push CU.size
    for wd in JW.getD k [] do
      CJ := CJ.push XW.size
      XW := XW.push wd
    JO := JO.push CJ.size
  let Xa := XW.map fun wd => evalW n GA wd
  let Xia := Xa.map invA
  let keyOf := fun (g : Array Nat) => base.foldl (fun a b => a * n + g[b]!) 0
  let repKeys := repOf.map fun j => keyOf els[j]!
  let mut RLc : Array (Array Nat) := Array.replicate ncl #[]
  for j in [0:N] do
    let x := els[j]!
    let k := keyOf (comp x x)
    match (Array.range ncl).find? (fun i => repKeys[i]! == k) with
    | some i => RLc := RLc.set! i (RLc[i]!.push j)
    | none => pure ()
  let mut RL : Array Nat := #[]
  let mut RC : Array Nat := #[]
  let mut RO : Array Nat := #[0]
  let mut RI : Array Nat := Array.replicate N 0
  for ci in [0:ncl] do
    for j in RLc[ci]! do
      RI := RI.set! j (RL.size + 1)
      RL := RL.push j
      RC := RC.push ci
    RO := RO.push RL.size
  let R := RL.size
  let siftR := fun (y : Array Nat) => Id.run do
    let mut g := y
    let mut ok := true
    for l in [0:L.size] do
      if ok then
        let b := base[l]!
        match (List.range L[l]!.size).find? (fun k => (L[l]!)[k]![b]! == g[b]!) with
        | some k => g := comp (invA (L[l]!)[k]!) g
        | none => ok := false
    return if ok then some g else none
  let mut CT : Array Nat := Array.replicate R 0
  let mut CP : Array Nat := Array.replicate R 0
  let mut nCut := 0
  for p in [0:R] do
    let ci := RC[p]!
    let x := els[RL[p]!]!
    let mut done := false
    for u in [0:UO[ci+1]! - UO[ci]!] do
      if !done then
        let t := CU[UO[ci]! + u]!
        let y := comp Xia[t]! (comp x Xa[t]!)
        match siftR y with
        | none =>
          CT := CT.set! p (u + 1)
          done := true
          nCut := nCut + 1
        | some g =>
          match (List.range n).find? (fun q => g[q]! != q) with
          | some q =>
            CT := CT.set! p (u + 1)
            CP := CP.set! p q
            done := true
            nCut := nCut + 1
          | none => pure ()
  let wordsOf := fun (A B : Array Nat) =>
    #[idA n, comp A A, A, comp A (comp A A), B, comp A (comp A B), comp A B,
      comp A (comp A (comp A B))]
  let mut QC : Array Nat := #[]
  let mut QJ : Array Nat := #[]
  let mut keys : Array (Array Nat) := #[]
  let mut nPairs := 0
  for ci in [0:ncl] do
    if ci != zc then
      let blk := (List.range (RO[ci+1]! - RO[ci]!)).map (· + RO[ci]!) |>.filter (CT[·]! == 0)
      for p in blk do
        for q in blk do
          let X := els[RL[p]!]!
          let Y := els[RL[q]!]!
          if comp X (comp Y X) == Y then
            nPairs := nPairs + 1
            let ws := wordsOf X Y
            let idx := ws.map (indexOf L base ·)
            let srt := idx.qsort (· < ·)
            if !(keys.contains srt) then
              keys := keys.push srt
              QC := QC.push ci
              QJ := QJ ++ idx
  let nq := QC.size
  let mut QW : Array Nat := Array.replicate (25 * nq) 0
  for mm in [0:nq] do
    let ci := QC[mm]!
    if JO[ci+1]! - JO[ci]! < 5 then
      throwError s!"#kss_rootpair: fewer than 5 conjugators for class {ci} (word {wOf[ci]!}); \
        {R} roots, {nCut} cut, {nPairs} pairs, classes of subgroups {QC}"
    let J := (List.range 8).map fun k => els[QJ[8 * mm + k]!]!
    for a in [0:5] do
      for b in [0:5] do
        if a < b then
          let ta := CJ[JO[ci]! + a]!
          let tb := CJ[JO[ci]! + b]!
          let cc := comp Xia[tb]! Xa[ta]!
          let cci := invA cc
          match (List.range 8).find? (fun k => !(J.contains (comp cc (comp J[k]! cci)))) with
          | some k => QW := QW.set! (25 * mm + 5 * a + b) k
          | none => throwError "#kss_rootpair: conjugates {a}, {b} of subgroup {mm} agree"
  let RP := (Array.range ncl).map fun ci => posOf[repOf[ci]!]!
  withSync do
    addTree (P ++ `GS) (GA.map (pack w))
    addTree (P ++ `GSI) (GA.map fun g => pack w (invA g))
    addTree (P ++ `RP) RP
    addDef (P ++ `zc) natT (lit zc)
    addDef (P ++ `nx) natT (lit XW.size)
    addTree (P ++ `X) (Xa.map (pack w))
    addTree (P ++ `XI) (Xia.map (pack w))
    addDef (P ++ `XWl) (mkApp (mkConst ``List [0]) listIntT) (listListIntE XW.toList)
    addDef (P ++ `XW) (mkForall `t .default natT listIntT) (mkLambda `t .default natT
      (mkAppN (mkConst ``List.getD [0]) #[listIntT, mkConst (P ++ `XWl), mkBVar 0,
        mkApp (mkConst ``List.nil [0]) (mkConst ``Int)]))
    addTree (P ++ `UO) UO
    addTree (P ++ `CU) CU
    addTree (P ++ `JO) JO
    addTree (P ++ `CJ) CJ
    addTree (P ++ `RL) RL
    addTree (P ++ `RC) RC
    addTree (P ++ `RI) RI
    addTree (P ++ `RO) RO
    addTree (P ++ `KL) repKeys
    addDef (P ++ `R) natT (lit R)
    addTree (P ++ `CT) CT
    addTree (P ++ `CP) CP
    addTree (P ++ `QC) QC
    addTree (P ++ `QJ) QJ
    addTree (P ++ `QW) QW
    addDef (P ++ `nq) natT (lit nq)

end
