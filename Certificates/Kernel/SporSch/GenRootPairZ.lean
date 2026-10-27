module

public import Certificates.Data.Kernel.SporSch.RootPairZ
public import CFSG.Certificates.Kernel.Spor.RawSound
public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Kernel.SporSch.J1.GenPt
public meta import Certificates.Kernel.SporSch.GenRootPair
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Kernel.SporSch.GenRootPair

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSch.MOCG CFSG.KS.SporSch.JPG CFSG.KS.SporSch.RPG in
elab "#kss_rootpairz " pre:ident nn:num ww:num sId:ident bId:ident zId:ident gId:ident
    xwId:ident tId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let S ← evalArrs sId
  let base ← evalArr bId
  let Zarr ← evalArr zId
  let GA ← evalArrs gId
  let XW ← evalLLI xwId
  let T ← evalArrs tId
  let L := levelsOf n S base
  let N := L.foldl (fun a T => a * T.size) 1
  let els := (Array.range N).map fun j => elemOf L n j
  let Xa := XW.toArray.map fun wd => evalW n GA wd
  let Xia := Xa.map invA
  let nx := Xa.size
  let keyOf := fun (g : Array Nat) => base.foldl (fun a b => a * n + g[b]!) 0
  let zk := keyOf Zarr
  let RL := (Array.range N).filter fun j => keyOf (comp els[j]! els[j]!) == zk
  let nr := RL.size
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
  let mut CT : Array Nat := Array.replicate nr 0
  let mut CP : Array Nat := Array.replicate nr 0
  for d in [0:nr] do
    let y := comp Xia[0]! (comp els[RL[d]!]! Xa[0]!)
    match siftR y with
    | none => CT := CT.set! d 1
    | some g =>
      match (List.range n).find? (fun q => g[q]! != q) with
      | some q =>
        CT := CT.set! d 1
        CP := CP.set! d q
      | none => pure ()
  let wordsOf := fun (A B : Array Nat) =>
    #[idA n, comp A A, A, comp A (comp A A), B, comp A (comp A B), comp A B,
      comp A (comp A (comp A B))]
  let idxOf := fun (g : Array Nat) =>
    let j := indexOf L base g
    if els[j]! == g then j else N
  let ntw := T.size / 2
  let mut QJ : Array Nat := #[]
  for i in [0:ntw] do
    QJ := QJ ++ (wordsOf T[2 * i]! T[2 * i + 1]!).map idxOf
  let kept := (Array.range nr).filter (CT[·]! == 0)
  let mut nPairs := 0
  let mut nTw := 0
  let mut QA : Array Nat := Array.replicate (5 * ntw) 0
  let mut QW : Array Nat := Array.replicate (25 * ntw) 0
  let mut QP : Array Nat := Array.replicate (25 * ntw) 0
  let mut PQ : Array Nat := Array.replicate (nr * nr) 0
  let mut subOf : Std.HashMap (Nat × Nat) Nat := {}
  for mm in [0:ntw] do
    let blk := QJ.extract (8 * mm) (8 * mm + 8)
    for a in blk do
      for b in blk do
        if a < N && b < N && !subOf.contains (a, b) then subOf := subOf.insert (a, b) mm
  for p in kept do
    for q in kept do
      let jx := RL[p]!
      let jy := RL[q]!
      let X := els[jx]!
      let Y := els[jy]!
      if comp X (comp Y X) == Y then
        nPairs := nPairs + 1
        let nq := QJ.size / 8
        let found := subOf.get? (jx, jy)
        if let some mm := found then
          PQ := PQ.set! (p * nr + q) mm
          if mm < ntw then nTw := nTw + 1
        else
          let J := wordsOf X Y
          let mm := nq
          let mut sel : Array Nat := #[]
          for t in [1:nx] do
            if sel.size < 5 then
              let ok := sel.all fun s =>
                let cc := comp Xia[t]! Xa[s]!
                let cci := invA cc
                J.any fun x => !(J.contains (comp cc (comp x cci)))
              if ok then sel := sel.push t
          if sel.size < 5 then
            throwError s!"#kss_rootpairz: pair ({jx}, {jy}) in no twin with {sel.size} conjugates"
          let mut qw : Array Nat := Array.replicate 25 0
          let mut qp : Array Nat := Array.replicate 25 0
          for a in [0:5] do
            for b in [0:5] do
              if a < b then
                let cc := comp Xia[sel[b]!]! Xa[sel[a]!]!
                let cci := invA cc
                let hit := (List.range 8).findSome? fun k =>
                  let y := comp cc (comp J[k]! cci)
                  ((List.range n).find? fun x => J.all fun t => t[x]! != y[x]!).map (k, ·)
                match hit with
                | some (k, x) =>
                  qw := qw.set! (5 * a + b) k
                  qp := qp.set! (5 * a + b) x
                | none => throwError "#kss_rootpairz: conjugates {a}, {b} of subgroup {mm}: no point"
          let Jx := J.map idxOf
          for a in Jx do
            for b in Jx do
              if !subOf.contains (a, b) then subOf := subOf.insert (a, b) mm
          PQ := PQ.set! (p * nr + q) mm
          QJ := QJ ++ Jx
          QA := QA ++ sel
          QW := QW ++ qw
          QP := QP ++ qp
  let nq := QJ.size / 8
  logInfo m!"#kss_rootpairz: {nr} roots, {kept.size} kept, {nPairs} pairs ({nTw} in twins), \
    {nq - ntw} subgroups"
  withSync do
    addDef (P ++ `nx) natT (lit nx)
    addTree (P ++ `X) (Xa.map (pack w))
    addTree (P ++ `XI) (Xia.map (pack w))
    addDef (P ++ `XWl) (mkApp (mkConst ``List [0]) listIntT) (listListIntE XW)
    addDef (P ++ `XW) (mkForall `t .default natT listIntT) (mkLambda `t .default natT
      (mkAppN (mkConst ``List.getD [0]) #[listIntT, mkConst (P ++ `XWl), mkBVar 0,
        mkApp (mkConst ``List.nil [0]) (mkConst ``Int)]))
    addTree (P ++ `CT) CT
    addTree (P ++ `CP) CP
    addTree (P ++ `QJ) QJ
    addTree (P ++ `QA) QA
    addTree (P ++ `QW) QW
    addTree (P ++ `QP) QP
    addTree (P ++ `PQ) PQ
    addDef (P ++ `nq) natT (lit nq)
    addDef (P ++ `ntw) natT (lit ntw)

end
