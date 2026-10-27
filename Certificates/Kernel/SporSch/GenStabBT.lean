module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Std.Data.HashMap
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.GenSetReplay
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Mathlib.Algebra.Group.Nat.Defs
public import Certificates.Data.Kernel.SporSch.StabBT
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Kernel.SporSch.GenSetReplay

open Lean Elab Command

public section

namespace CFSG.KS.SporSchBT

open CFSG.KC.Tab CFSG.KS.RawGen

meta partial def sparse (ks : Array (Nat × Nat)) (lo hi : Nat) : Expr :=
  if hi ≤ lo then constFn (lit 0)
  else if hi = lo + 1 then
    let (k, v) := ks[lo]!
    let motive := mkLambda `_ .default (mkConst ``Bool) natT
    mkLambda `i .default natT (mkAppN (mkConst ``Bool.rec [Level.one])
      #[motive, lit 0, lit (v + 1), mkApp2 (mkConst ``Nat.beq) (mkBVar 0) (lit k)])
  else
    let mid := (lo + hi) / 2
    node (sparse ks lo mid) (sparse ks mid hi) ks[mid]!.1

meta def cntBTm (n : Nat) (pts : Array (Array Nat)) (trs : Array (Array (Array Nat)))
    (inL : Nat → Bool) : Nat → Nat → Array Nat → Nat
  | 0, _, _ => 1
  | f + 1, i, h => Id.run do
    let mut acc := 0
    for k in [0:pts[i]!.size] do
      if inL h[(pts[i]!)[k]!]! then
        acc := acc + cntBTm n pts trs inL f (i + 1) (comp n h (trs[i]!)[k]!)
    return acc

meta def intE (z : Int) : Expr :=
  if 0 ≤ z then mkApp (mkConst ``Int.ofNat) (lit z.toNat)
  else mkApp (mkConst ``Int.negSucc) (lit ((-z).toNat - 1))

meta def wordsE (ws : Array (List Int)) : Expr :=
  let intT := mkConst ``Int
  let lT := mkApp (mkConst ``List [0]) intT
  let w1 := fun (wd : List Int) => wd.foldr (fun z acc => mkApp3 (mkConst ``List.cons [0]) intT (intE z) acc)
    (mkApp (mkConst ``List.nil [0]) intT)
  ws.foldr (fun wd acc => mkApp3 (mkConst ``List.cons [0]) lT (w1 wd) acc) (mkApp (mkConst ``List.nil [0]) lT)

end CFSG.KS.SporSchBT

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGen CFSG.KS.SporSchBT in
elab "#kss_btstab " pre:ident nn:num ww:num aId:ident lId:ident ord:num sd:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let order := ord.getNat
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let lN ← liftCoreM <| realizeGlobalConstNoOverload lId
  let A ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) aN
  let L ← liftTermElabM <| unsafe evalConst (List Nat) lN
  let kO := A.size
  let ident := Array.range n
  let mut S : Array (Array Nat) := A
  let mut W : Array (List Int) := A.map fun _ => []
  let mut base : Array Nat := L.toArray
  let levelsOf := fun (S : Array (Array Nat)) (base : Array Nat) => Id.run do
    let mut out : Array (Std.HashMap Nat (Array Nat × List Int)) := #[]
    for i in [0:base.size] do
      let idx := (List.range S.size).filter fun j =>
        (List.range i).all fun t => (S[j]!)[base[t]!]! == base[t]!
      let steps : Array (Array Nat × Int) :=
        (idx.map fun (j : Nat) => (S[j]!, ((j + 1 : Nat) : Int))).toArray ++
        (idx.map fun (j : Nat) => (inv n S[j]!, -(((j + 1 : Nat) : Int)))).toArray
      let b := base[i]!
      let mut tr : Std.HashMap Nat (Array Nat × List Int) := (∅ : Std.HashMap Nat _).insert b (ident, [])
      let mut q : Array Nat := #[b]
      let mut h := 0
      while h < q.size do
        let x := q[h]!
        let (tx, wx) := tr.get! x
        for (s, l) in steps do
          let y := s[x]!
          if !tr.contains y then
            tr := tr.insert y (comp n s tx, l :: wx)
            q := q.push y
        h := h + 1
      out := out.push tr
    return out
  let mut lv := levelsOf S base
  let sizeOf := fun (lv : Array (Std.HashMap Nat (Array Nat × List Int))) =>
    lv.foldl (fun acc t => acc * t.size) 1
  let mut st := sd.getNat
  let mut guard := 0
  while sizeOf lv < order && guard < 10000 do
    guard := guard + 1
    let mut r := ident
    let mut rw : List Int := []
    for _ in [0:40] do
      st := (st * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
      let j := (st >>> 33) % kO
      r := comp n A[j]! r
      rw := ((j + 1 : Nat) : Int) :: rw
    let mut g := r
    let mut gw := rw
    let mut lvl := base.size
    for i in [0:base.size] do
      let y := g[base[i]!]!
      match lv[i]!.get? y with
      | some (t, tw) =>
        g := comp n (inv n t) g
        gw := (tw.reverse.map fun z => -z) ++ gw
      | none =>
        if lvl == base.size then lvl := i
    if lvl == base.size && g != ident then
      let moved := (List.range n).find? fun x => g[x]! != x
      base := base.push moved.get!
    if g != ident then
      S := S.push g
      W := W.push gw
      lv := levelsOf S base
  let kS := S.size
  let nb := base.size
  let Sinv := S.map (inv n)
  let mut recs : Array Nat := #[]
  let mut trs : Array Nat := #[]
  let mut tris : Array Nat := #[]
  let mut trArr : Array (Array (Array Nat)) := #[]
  let mut ptsArr : Array (Array Nat) := #[]
  let nw := n * w
  for i in [0:nb] do
    let idx := (List.range kS).filter fun j => (List.range i).all fun t => (S[j]!)[base[t]!]! == base[t]!
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
    trArr := trArr.push tr
    ptsArr := ptsArr.push pts
    for k in [0:c] do
      trs := trs.push (pack w tr[k]!)
      tris := tris.push (pack w (inv n tr[k]!))
  let D := W.extract kO kS
  let m := L.length
  let inL := fun (x : Nat) => L.contains x
  let cntT := cntBTm n ptsArr trArr inL
  let mut leaves : Array (Nat × Nat) := #[]
  for k0 in [0:ptsArr[0]!.size] do
    if inL (ptsArr[0]!)[k0]! then
      let h0 := (trArr[0]!)[k0]!
      for k1 in [0:ptsArr[1]!.size] do
        if inL h0[(ptsArr[1]!)[k1]!]! then
          let h1 := comp n h0 (trArr[1]!)[k1]!
          for k2 in [0:ptsArr[2]!.size] do
            if inL h1[(ptsArr[2]!)[k2]!]! then
              let h2 := comp n h1 (trArr[2]!)[k2]!
              leaves := leaves.push ((k0 <<< 18) ||| (k1 <<< 9) ||| k2, cntT (m - 3) 3 h2)
  let nReal := leaves.size
  let N := leaves.foldl (fun a p => a + p.2) 0
  let sorted := ((Array.range nReal).map fun j => (leaves[j]!.1, j)).qsort (fun a b => a.1 < b.1)
  let SP := L.foldl (fun acc x => acc ||| (1 <<< x)) 0
  let nG := (nReal + 15) / 16
  let nL := 16 * nG
  let leavesP := leaves ++ Array.replicate (nL - nReal) leaves[nReal - 1]!
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `S) (S.map (pack w))
    addTree (P ++ `SI) (Sinv.map (pack w))
    addTree (P ++ `LR) recs
    addTree (P ++ `TR) trs
    addTree (P ++ `TRI) tris
    addDef (P ++ `BP) natT (lit (pack w base))
    let lT := mkApp (mkConst ``List [0]) (mkApp (mkConst ``List [0]) (mkConst ``Int))
    addDef (P ++ `D) lT (wordsE D)
    addDef (P ++ `kS) natT (lit kS)
    addDef (P ++ `nb) natT (lit nb)
    addDef (P ++ `KV) fnT (sparse sorted 0 sorted.size)
    addTree (P ++ `KJ) (leavesP.map (·.1))
    addTree (P ++ `VT) (leavesP.map (·.2))
    addDef (P ++ `nL) natT (lit nL)
    addDef (P ++ `N) natT (lit N)
    addDef (P ++ `SP) natT (lit SP)
    addDef (P ++ `nG) natT (lit nG)
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
      #[nE, wE, mE, nwE, idE, c `S, c `SI, kSE, lit kO, c `D, nbE, c `BP])
    CFSG.KC.addThmDecl <| { name := P ++ `head, levelParams := [], type := headT, value := reflBoolTrue }
    let stepsE := fun (iE : Expr) => mkAppN (mkConst ``CFSG.KS.Raw.stepsAt) #[nE, wE, c `S, kSE, c `BP, iE]
    let lvT := fun (iE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.Raw.levelK)
      #[nE, wE, mE, nwE, pmE, idE, c `S, c `SI, c `TR, c `TRI, kSE,
        mkAppN (mkConst ``CFSG.KC.Enum.pg) #[wE, mE, c `BP, iE], stepsE iE, mkApp (c `LR) iE])
    for i in [0:nb] do
      let nm := P ++ Name.mkSimple s!"lv{i}"
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := lvT (lit i), value := reflBoolTrue }
    let lvP := mkLambda `i .default natT (lvT (mkBVar 0))
    let hlV := forallChain lvP nb fun i => mkConst (P ++ Name.mkSimple s!"lv{i}")
    let hlT := mkAppN (mkConst ``CFSG.KS.Raw.LevelsOK) #[nE, wE, c `S, c `SI, c `LR, c `TR, c `TRI, kSE, nbE, c `BP]
    CFSG.KC.addThmDecl <| { name := P ++ `hl, levelParams := [], type := hlT, value := hlV }
    let topT := mkApp3 (mkConst ``Eq [1]) natT
      (mkAppN (mkConst ``CFSG.KS.SporSch.btTop) #[nE, wE, c `LR, c `TR, c `SP, c `KV, c `KJ, c `VT, c `nL])
      (c `N)
    let topV := mkApp2 (mkConst ``Eq.refl [1]) natT (c `N)
    let topN := P ++ `top
    CFSG.KC.addThmDecl <| { name := topN, levelParams := [], type := topT, value := topV }
    let leafT := fun (jE : Expr) => isTrue (mkAppN (mkConst ``CFSG.KS.SporSch.btLeaf)
      #[nE, wE, c `LR, c `TR, c `SP, lit m, c `KJ, c `VT, jE])
    addChain2 P "leaf" "hleaf" nG 16 leafT

end
