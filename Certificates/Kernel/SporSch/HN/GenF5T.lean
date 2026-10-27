module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.SporSch.HN.GenF5
public import Certificates.Data.Kernel.SporSch.HNF5Kron
public import Certificates.Kernel.SporSch.HN.GenF5

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.SporSchGenF5 in
elab "#kss_f5tree " pre:ident mId:ident sId:ident : command => do
  let P := pre.getId
  let mN ← liftCoreM <| realizeGlobalConstNoOverload mId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let M ← liftTermElabM <| unsafe evalConst (List (Array (Array Nat))) mN
  let spec ← liftTermElabM <| unsafe evalConst (List (Nat × Nat × Nat)) sN
  let rows := M.foldl (fun acc m => acc ++ m.map pack16) #[]
  let ops := (spec.map fun (op, _, _) => op).toArray
  let ls := (spec.map fun (_, l, _) => l).toArray
  let rs := (spec.map fun (_, _, r) => r).toArray
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `MT) rows
    addTree (P ++ `OP) ops
    addTree (P ++ `L) ls
    addTree (P ++ `R) rs
