module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.BfsPin
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.KC.BfsGen

open CFSG.KC.Tab CFSG.KS.RawGen

meta def search (n w : Nat) (gens : Array (Array Nat)) : Array (Array Nat) × Array (Array Nat) :=
  Id.run do
    let id := Array.ofFn (n := n) fun i => i.val
    let mut pts : Array (Array Nat) := #[id]
    let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert (pack w id) 0
    let mut edges : Array (Array Nat) := #[]
    let mut i := 0
    while i < pts.size do
      let mut row := #[]
      for g in gens do
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

elab "#lc_bfs " pre:ident gId:ident n:num w:num : command => do
  let P := pre.getId
  let n := n.getNat
  let w := w.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let gs ← liftTermElabM <| unsafe evalConst (List (Array Nat)) gN
  let gens := gs.toArray
  let (pts, edges) := search n w gens
  let tv := pts.map (pack w)
  let ev := edges.map (pack 16)
  let order := ((Array.range tv.size).qsort fun a b => tv[a]! < tv[b]!)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `G) (gens.map (pack w))
    addDef (P ++ `ng) natT (lit gens.size)
    addDef (P ++ `N) natT (lit tv.size)
    addTree (P ++ `T) tv
    addTree (P ++ `E) ev
    addTree (P ++ `S) order
    let ty := isTrue (mkAppN (mkConst ``CFSG.KC.BfsPin.bfsK)
      #[lit n, lit w, mkConst (P ++ `ng), mkConst (P ++ `G), mkConst (P ++ `N), mkConst (P ++ `T),
        mkConst (P ++ `E), mkConst (P ++ `S)])
    CFSG.KC.addThmDecl <| { name := P ++ `ok, levelParams := [], type := ty, value := reflBoolTrue }

end CFSG.KC.BfsGen

end
