module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.ConjOrb
public import Certificates.Data.Kernel.BfsPinKeys
public import Certificates.Data.Kernel.Misc.PermClos
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Mathlib.GroupTheory.Perm.Basic
meta import Mathlib.Data.List.Monad

open Lean Elab Command

public section

namespace CFSG.KC.ConjOrbGen

open CFSG.KC.Tab CFSG.KS.RawGen

meta def conj (n : Nat) (g t : Array Nat) : Array Nat := comp n g (comp n t (inv n g))

meta def search (n w : Nat) (gens : Array (Array Nat)) (root : Array Nat) :
    Array (Array Nat) × Array (Array Nat) := Id.run do
  let mut pts : Array (Array Nat) := #[root]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert (pack w root) 0
  let mut edges : Array (Array Nat) := #[]
  let mut i := 0
  while i < pts.size do
    let mut row := #[]
    for g in gens do
      let y := conj n g pts[i]!
      match idx.get? (pack w y) with
      | some j => row := row.push j
      | none =>
        idx := idx.insert (pack w y) pts.size
        row := row.push pts.size
        pts := pts.push y
    edges := edges.push row
    i := i + 1
  return (pts, edges)

meta def treeOf (edges : Array (Array Nat)) (t r : Nat) : Option (Array Nat) := Id.run do
  let N := edges.size
  let mut rs : Array Nat := Array.replicate N 0
  let mut seen : Array Bool := (Array.replicate N false).set! r true
  let mut q : Array Nat := #[r]
  let mut h := 0
  let mut dep : Array Nat := Array.replicate N 0
  while h < q.size do
    let x := q[h]!
    for l in [0:t] do
      let y := edges[x]![l]!
      if !seen[y]! then
        seen := seen.set! y true
        dep := dep.set! y (dep[x]! + 1)
        rs := rs.set! y (x ||| (l <<< 20) ||| ((dep[x]! + 1) <<< 24))
        q := q.push y
    h := h + 1
  if q.size == N then return some rs else return none

meta def blocks (bw : Nat) (vs : Array Nat) : Array Nat :=
  (Array.range ((vs.size + 63) / 64)).map fun b => Id.run do
    let mut acc := 0
    for t in [0:64] do
      let k := 64 * b + t
      if k < vs.size then
        acc := acc ||| (vs[k]! <<< (bw * t))
    return acc

meta def blkE (F : Name) (bw : Nat) : Expr :=
  mkApp2 (mkConst ``CFSG.KC.ConjOrb.blk) (mkConst F) (lit bw)

end CFSG.KC.ConjOrbGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KC.ConjOrbGen in
elab "#conj_orb " pre:ident gId:ident nn:num ww:num psId:ident ll:num " roots " rs:ident*
    " gens " ts:num* : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let L := ll.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let gens ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let psN ← liftCoreM <| realizeGlobalConstNoOverload psId
  let ps ← liftTermElabM <| unsafe evalConst (List Nat) psN
  let mut roots : Array (Array Nat) := #[]
  for r in rs do
    let rN ← liftCoreM <| realizeGlobalConstNoOverload r
    roots := roots.push (← liftTermElabM <| unsafe evalConst (Array Nat) rN)
  unless roots.size == ts.size && 0 < roots.size do
    throwError "#conj_orb: give one generator count per root"
  let (pts, edges) := search n w gens roots[0]!
  let N := pts.size
  unless L > 0 && N % L == 0 do throwError "#conj_orb: {N} points, slices of {L}"
  let K := N / L
  let ng := gens.size
  let tv := pts.map (pack w)
  let idxOf : Std.HashMap Nat Nat := (Array.range N).foldl (fun m i => m.insert tv[i]! i) {}
  let mut trees : Array (Nat × Nat × Array Nat) := #[]
  for j in [0:roots.size] do
    let t := ts[j]!.getNat
    let some r := idxOf.get? (pack w roots[j]!) | throwError "#conj_orb: root {j} not in the class"
    let some D := treeOf edges t r | throwError "#conj_orb: root {j} does not reach the class"
    trees := trees.push (r, t, D)
  let keyOf := fun (a : Array Nat) => ps.foldr (fun p acc => a[p]! + n * acc) 0
  let order := ((Array.range N).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!)
  let nE := lit n
  let wE := lit w
  let c := fun (s : Name) => mkConst (P ++ s)
  let thm := fun (nm : Name) (ty : Expr) =>
    CFSG.KC.addThmDecl <| { name := P ++ nm, levelParams := [], type := ty, value := reflBoolTrue }
  let closF := mkAppN (mkConst ``CFSG.KC.ConjOrb.closPt)
    #[nE, wE, c `ng, c `N, c `G, c `GI, c `T, c `E]
  let allRE := fun (f : Expr) (s : Nat) =>
    isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Clos.allR) #[mulE (lit L) (lit s), lit L, f])
  let joined := fun (nm : Name) (f : Expr) (slice : Nat → Name) => do
    let Pf := mkLambda `s .default natT
      (isTrue (mkAppN (mkConst ``CFSG.KC.Misc.Clos.allR) #[mulE (lit L) (mkBVar 0), lit L, f]))
    let hP := forallChain Pf K fun s => mkConst (P ++ slice s)
    let ty := mkForall `i .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, mulE (lit L) (lit K)])
      (isTrue (mkApp f (mkBVar 1))))
    let pf := mkAppN (mkConst ``CFSG.KC.Misc.Clos.forall_of_chunks) #[lit L, lit K, f, hP]
    CFSG.KC.addThmDecl <| { name := P ++ nm, levelParams := [], type := ty, value := pf }
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `G) (gens.map (pack w))
    addTree (P ++ `GI) (gens.map fun g => pack w (inv n g))
    addDef (P ++ `ng) natT (lit ng)
    addDef (P ++ `N) natT (lit N)
    addTree (P ++ `TL) (blocks (n * w) tv)
    addDef (P ++ `T) fnT (blkE (P ++ `TL) (n * w))
    addTree (P ++ `EL) (blocks 64 (edges.map (pack 20)))
    addDef (P ++ `E) fnT (blkE (P ++ `EL) 64)
    addTree (P ++ `SL) (blocks 32 order)
    addDef (P ++ `S) fnT (blkE (P ++ `SL) 32)
    for j in [0:trees.size] do
      let (r, _, D) := trees[j]!
      addDef (P ++ Name.mkSimple s!"r{j}") natT (lit r)
      addTree (P ++ Name.mkSimple s!"D{j}L") (blocks 32 D)
      addDef (P ++ Name.mkSimple s!"D{j}") fnT (blkE (P ++ Name.mkSimple s!"D{j}L") 32)
    thm `h (isTrue (mkAppN (mkConst ``CFSG.KC.ConjOrb.headK) #[nE, wE, c `ng, c `G, c `GI]))
    let keyF := mkLambda `i .default natT (mkAppN (mkConst ``CFSG.KC.BfsPin.pkeyK)
      #[nE, wE, mkConst psN, mkApp (c `T) (mkBVar 0)])
    thm `k (isTrue (mkAppN (mkConst ``CFSG.KC.BfsPin.distinctK) #[c `N, keyF, c `S]))
    for s in [0:K] do
      thm (Name.mkSimple s!"c{s}") (allRE closF s)
    joined `cl closF fun s => Name.mkSimple s!"c{s}"
    for j in [0:trees.size] do
      let (_, t, _) := trees[j]!
      let trF := mkAppN (mkConst ``CFSG.KC.ConjOrb.treePt)
        #[lit t, c `N, c (Name.mkSimple s!"r{j}"), c `E, c (Name.mkSimple s!"D{j}")]
      for s in [0:K] do
        thm (Name.mkSimple s!"t{j}_{s}") (allRE trF s)
      joined (Name.mkSimple s!"tr{j}") trF fun s => Name.mkSimple s!"t{j}_{s}"

end
