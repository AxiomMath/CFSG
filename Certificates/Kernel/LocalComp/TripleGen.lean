module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.TripleOrbit
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.KC.TripleGen

open CFSG.KC.Tab CFSG.KS.RawGen

meta def cd (t : Nat × Nat × Nat) : Nat := t.1 + 32 * t.2.1 + 1024 * t.2.2

meta def records (a b : Array Nat) : Array Nat := Id.run do
  let gens := #[a, b]
  let mut seen : Std.HashMap Nat (Nat × Nat × Nat) := {}
  let mut queue : Array (Nat × Nat × Nat) := #[(0, 1, 2)]
  seen := seen.insert (cd (0, 1, 2)) (0, 0, 0)
  let mut h := 0
  while h < queue.size do
    let t := queue[h]!
    h := h + 1
    let (_, _, dt) := seen.getD (cd t) (0, 0, 0)
    for g in [0:2] do
      let G := gens[g]!
      let u := (G[t.1]!, G[t.2.1]!, G[t.2.2]!)
      if !seen.contains (cd u) then
        seen := seen.insert (cd u) (cd t, g, dt + 1)
        queue := queue.push u
  let codes := (queue.map cd).qsort (· < ·)
  let mut pos : Std.HashMap Nat Nat := {}
  for i in [0:codes.size] do
    pos := pos.insert codes[i]! i
  let mut out := #[]
  for c in codes do
    let (pc, g, d) := seen.getD c (0, 0, 0)
    out := out.push (c ||| (pos.getD pc 0 <<< 15) ||| (g <<< 29) ||| (d <<< 30))
  return out

elab "#lc_triples " pre:ident aId:ident bId:ident : command => do
  let P := pre.getId
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let a ← liftTermElabM <| unsafe evalConst (Array Nat) aN
  let b ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  let rs := records a b
  let leaves := Id.run do
    let mut ls := #[]
    for k in [0:(rs.size + 63) / 64] do
      let mut v := 0
      for j in [0:64] do
        if 64 * k + j < rs.size then v := v ||| (rs[64 * k + j]! <<< (36 * j))
      ls := ls.push v
    return ls
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `G0) natT (lit (pack 5 a))
    addDef (P ++ `G1) natT (lit (pack 5 b))
    addTree (P ++ `T) leaves
    addDef (P ++ `N) natT (lit rs.size)
    let ty := isTrue (mkAppN (mkConst ``CFSG.KC.Triple.treeOK)
      #[mkConst (P ++ `G0), mkConst (P ++ `G1), mkConst (P ++ `T), mkConst (P ++ `N), lit 145])
    CFSG.KC.addThmDecl <| { name := P ++ `ok, levelParams := [], type := ty, value := reflBoolTrue }

end CFSG.KC.TripleGen

end
