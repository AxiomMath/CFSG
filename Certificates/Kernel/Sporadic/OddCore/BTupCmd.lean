module

public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public import Certificates.Data.Kernel.Spor.BTup
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.KS.BTupGen

open CFSG.KS.RawGen

meta def rowsW (fw : Nat) (a : Array Nat) : Array Nat :=
  (List.range ((a.size + 31) / 32)).toArray.map fun r =>
    pack fw ((List.range 32).toArray.map fun t => a.getD (32 * r + t) 0)

end CFSG.KS.BTupGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.BTupGen in
elab "#kbtup " pre:ident nn:num ww:num gId:ident bId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let gens ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let base ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  let k := gens.size
  let d := base.size
  if base.any (· ≥ n) then throwError "#kbtup: a base point is not below {n}"
  let key : Array Nat → Nat := pack w
  let mut sts : Array (Array Nat) := #[base]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut dep : Array Nat := #[0]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert (key base) 0
  let mut q := 0
  while q < sts.size do
    let t := sts[q]!
    for j in [0:k] do
      let u := t.map fun x => gens[j]![x]!
      let ku := key u
      if !idx.contains ku then
        idx := idx.insert ku sts.size
        sts := sts.push u
        par := par.push q
        lab := lab.push j
        dep := dep.push (dep[q]! + 1)
    q := q + 1
  let cnt := sts.size
  let keys := sts.map key
  let srt := (List.range cnt).toArray.qsort fun a b => keys[a]! < keys[b]!
  let mut pos := Array.replicate cnt 0
  for s in [0:cnt] do
    pos := pos.set! srt[s]! s
  let sKeys := srt.map fun i => keys[i]!
  let recs := srt.map fun i =>
    lab[i]! + 256 * pos[par[i]!]! + 1099511627776 * dep[i]!
  let imgs := (srt.map fun i => (List.range k).toArray.map fun j =>
    pos[idx.getD (key (sts[i]!.map fun x => gens[j]![x]!)) 0]!).flatten
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `G) (gens.map (pack w))
    addDef (P ++ `B) natT (lit (key base))
    addTree (P ++ `K) (rowsW (w * d) sKeys)
    addTree (P ++ `R) (rowsW 64 recs)
    addTree (P ++ `POS) (rowsW 32 imgs)
    addDef (P ++ `cnt) natT (lit cnt)

end
