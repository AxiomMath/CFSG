module

public import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public import Certificates.Data.Kernel.LeftOrb
public meta import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.KC.LeftOrbGen

open CFSG.KC.Tab CFSG.KS.RawGen

meta def search (n w : Nat) (gs : Array (Array Nat)) :
    Array (Array Nat) × Array (Array Nat) := Id.run do
  let root := Array.range n
  let mut pts : Array (Array Nat) := #[root]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert (pack w root) 0
  let mut edges : Array (Array Nat) := #[]
  let mut i := 0
  while i < pts.size do
    let mut row := #[]
    for g in gs do
      let y := comp n g pts[i]!
      match idx.get? (pack w y) with
      | some j => row := row.push j
      | none =>
        idx := idx.insert (pack w y) pts.size
        row := row.push pts.size
        pts := pts.push y
    edges := edges.push row
    i := i + 1
  return (pts, edges)

end CFSG.KC.LeftOrbGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KC.ConjOrbGen CFSG.KC.LeftOrbGen in
elab "#left_orb " pre:ident gId:ident nn:num ww:num psId:ident ll:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let L := ll.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let gs ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let psN ← liftCoreM <| realizeGlobalConstNoOverload psId
  let ps ← liftTermElabM <| unsafe evalConst (List Nat) psN
  let (pts, edges) := CFSG.KC.LeftOrbGen.search n w gs
  let N := pts.size
  unless L > 0 && N % L == 0 do throwError "#left_orb: {N} points, slices of {L}"
  let K := N / L
  let ng := gs.size
  let tv := pts.map (pack w)
  let some D := treeOf edges ng 0 | throwError "#left_orb: the search is not connected"
  let keyOf := fun (a : Array Nat) => ps.foldr (fun p acc => a[p]! + n * acc) 0
  let order := ((Array.range N).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!)
  let nE := lit n
  let wE := lit w
  let c := fun (s : Name) => mkConst (P ++ s)
  let thm := fun (nm : Name) (ty : Expr) =>
    CFSG.KC.addThmDecl <| { name := P ++ nm, levelParams := [], type := ty, value := reflBoolTrue }
  let closF := mkAppN (mkConst ``CFSG.KC.LeftOrb.closPtL) #[nE, wE, c `ng, c `N, c `G, c `T, c `E]
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
    addTree (P ++ `G) (gs.map (pack w))
    addTree (P ++ `GI) (gs.map fun g => pack w (inv n g))
    addDef (P ++ `ng) natT (lit ng)
    addDef (P ++ `N) natT (lit N)
    addTree (P ++ `TL) (blocks (n * w) tv)
    addDef (P ++ `T) fnT (blkE (P ++ `TL) (n * w))
    addTree (P ++ `EL) (blocks (20 * ng) (edges.map (pack 20)))
    addDef (P ++ `E) fnT (blkE (P ++ `EL) (20 * ng))
    addTree (P ++ `SL) (blocks 32 order)
    addDef (P ++ `S) fnT (blkE (P ++ `SL) 32)
    addTree (P ++ `DL) (blocks 32 D)
    addDef (P ++ `D) fnT (blkE (P ++ `DL) 32)
    thm `h (isTrue (mkAppN (mkConst ``CFSG.KC.ConjOrb.headK) #[nE, wE, c `ng, c `G, c `GI]))
    let keyF := mkLambda `i .default natT (mkAppN (mkConst ``CFSG.KC.BfsPin.pkeyK)
      #[nE, wE, mkConst psN, mkApp (c `T) (mkBVar 0)])
    thm `k (isTrue (mkAppN (mkConst ``CFSG.KC.BfsPin.distinctK) #[c `N, keyF, c `S]))
    for s in [0:K] do
      thm (Name.mkSimple s!"c{s}") (allRE closF s)
    joined `cl closF fun s => Name.mkSimple s!"c{s}"
    let trF := mkAppN (mkConst ``CFSG.KC.ConjOrb.treePt) #[lit ng, c `N, lit 0, c `E, c `D]
    for s in [0:K] do
      thm (Name.mkSimple s!"t{s}") (allRE trF s)
    joined `tr trF fun s => Name.mkSimple s!"t{s}"

end
