module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.LocalComp.BfsGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kbfs_data " pre:ident nn:num ww:num gId:ident pId:ident ll:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let L := ll.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let pN ← liftCoreM <| realizeGlobalConstNoOverload pId
  let gs ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let ps ← liftTermElabM <| unsafe evalConst (List Nat) pN
  let (pts, rows) := CFSG.KC.BfsGen.search n w gs
  let N := pts.size
  let tv := pts.map (pack w)
  let order := (Array.range N).qsort fun a b => tv[a]! < tv[b]!
  let K := (N + L - 1) / L
  let counts := (Array.range (K + 1)).map fun s =>
    (rows.extract 0 (L * s)).foldl (fun m r => r.foldl max m) 0 + 1
  let key := fun (a : Array Nat) => ps.foldr (fun p acc => a[p]! + n * acc) 0
  let skt := (Array.range N).qsort fun a b => key pts[a]! < key pts[b]!
  withSync do
    addTree (P ++ `G) (gs.map (pack w))
    addTree (P ++ `T) tv
    addTree (P ++ `E) (rows.map (pack 16))
    addTree (P ++ `S) order
    addTree (P ++ `C) counts
    addTree (P ++ `SKT) skt
    addDef (P ++ `N) natT (lit N)

end
