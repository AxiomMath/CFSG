module

public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Lean
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

namespace CFSG.KS.PEnumGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.PSL3Four.Native

meta def rows32 (a : Array Nat) : Array Nat :=
  (List.range ((a.size + 31) / 32)).toArray.map fun r =>
    pack 32 ((List.range 32).toArray.map fun t => a.getD (32 * r + t) 0)

end CFSG.KS.PEnumGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.PEnumGen CFSG.PSL3Four.Native in
elab "#kpenum " pre:ident nn:num ww:num cj:ident gId:ident giId:ident rId:ident cp:num :
    command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let conj := cj.getId == `true
  let cap := cp.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let giN ← liftCoreM <| realizeGlobalConstNoOverload giId
  let rN ← liftCoreM <| realizeGlobalConstNoOverload rId
  let gens ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let ginv ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) giN
  let root ← liftTermElabM <| unsafe evalConst (Array Nat) rN
  let k := gens.size
  let step : Nat → Tab → Tab := fun j t =>
    if conj then conjTab n gens[j]! ginv[j]! t else CFSG.PSL3Four.Native.comp n gens[j]! t
  let E := bfs step k root cap
  let cnt := E.tabs.size
  let idx := indexOf E.tabs
  let pl := (List.range cnt).toArray.map fun i => 4096 * E.par[i]! + E.lab[i]!
  let pos := ((List.range cnt).toArray.map fun h =>
    (List.range k).toArray.map fun j => idx.getD (step j E.tabs[h]!) cnt).flatten
  let keys := E.tabs.map (pack w)
  let srt := ((List.range cnt).toArray.qsort fun a b => keys[a]! < keys[b]!)
  let sri := Id.run do
    let mut r := Array.replicate cnt 0
    for s in [0:cnt] do
      r := r.set! srt[s]! s
    return r
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `T) keys
    addTree (P ++ `G) (gens.map (pack w))
    addTree (P ++ `GI) (ginv.map (pack w))
    addDef (P ++ `R) natT (lit (pack w root))
    addTree (P ++ `PL) (rows32 pl)
    addTree (P ++ `POS) (rows32 pos)
    addTree (P ++ `SRT) (rows32 srt)
    addTree (P ++ `SRI) (rows32 sri)
    addDef (P ++ `cnt) natT (lit cnt)
    addDef (P ++ `k) natT (lit k)

end
