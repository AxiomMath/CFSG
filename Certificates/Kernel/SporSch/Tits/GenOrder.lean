module

public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kst_order " pre:ident ww:num vv:num fId:ident : command => do
  let P := pre.getId
  let w := ww.getNat
  let V := vv.getNat
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let f ← liftTermElabM <| unsafe evalConst (Nat → Nat) fN
  let vals := (Array.range V).map f
  let so := (Array.range V).qsort fun a b => vals[a]! < vals[b]! || (vals[a]! == vals[b]! && a < b)
  let soi := Id.run do
    let mut r := Array.replicate V 0
    for i in [0:V] do
      r := r.set! so[i]! i
    return r
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `SO) natT (lit (pack w so))
    addDef (P ++ `SOI) natT (lit (pack w soi))
