module

public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KC.Co3BfsGen

open CFSG.KC.Tab CFSG.KS.RawGen

meta def comp (t u : Array Nat) : Array Nat := u.map fun x => t[x]!

meta def inv (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate t.size 0
  for i in [0:t.size] do
    r := r.set! t[i]! i
  return r

meta def key (np : Nat) (t : Array Nat) : Nat :=
  (List.range np).foldl (fun acc p => acc * 276 + t[p]!) 0

elab "#lc_bfs " pre:ident lId:ident pId:ident bId:ident gId:ident md:num : command => do
  let P := pre.getId
  let get (i : Ident) := liftCoreM <| realizeGlobalConstNoOverload i
  let lN ← get lId
  let pN ← get pId
  let bN ← get bId
  let gN ← get gId
  let L ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) lN
  let par ← liftTermElabM <| unsafe evalConst (Array Nat) pN
  let lab ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  let gs ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let mode := md.getNat
  let ng := if mode == 0 then 3 else 7
  let np := if mode == 0 then 2 else 4
  let gens := gs.extract 0 ng
  let mut idx : Std.HashMap Nat Nat := {}
  for k in [0:L.size] do
    idx := idx.insert (key np L[k]!) k
  let mut K := #[]
  for q in [0:L.size] do
    for i in [0:ng] do
      let y := if mode == 0 then comp L[q]! gens[i]! else comp (inv gens[i]!) (comp L[q]! gens[i]!)
      K := K.push (idx.getD (key np y) L.size)
  let S := ((Array.range L.size).qsort fun a b => key np L[a]! < key np L[b]!)
  let mut SI := Array.replicate L.size 0
  for m in [0:S.size] do
    SI := SI.set! S[m]! m
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `E) (L.map (pack 9))
    addTree (P ++ `P) par
    addTree (P ++ `L) lab
    addTree (P ++ `K) K
    addTree (P ++ `S) S
    addTree (P ++ `SI) SI
    addTree (P ++ `G) (gens.map (pack 9))
    addDef (P ++ `c) natT (lit L.size)

end CFSG.KC.Co3BfsGen

end
