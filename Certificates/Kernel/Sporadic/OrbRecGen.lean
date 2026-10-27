module

public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Std.Data.HashMap
public meta import Lean
public import Lean.Exception

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kc_orbrec " pre:ident rId:ident gId:ident kk:num ww:num : command => do
  let P := pre.getId
  let k := kk.getNat
  let w := ww.getNat
  let rN ← liftCoreM <| realizeGlobalConstNoOverload rId
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let R ← liftTermElabM <| unsafe evalConst (Array Nat) rN
  let gs ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let N := R.size
  let pos : Std.HashMap Nat Nat := Id.run do
    let mut m : Std.HashMap Nat Nat := ∅
    for i in [0:N] do
      m := m.insert R[i]! i
    return m
  let mut tabs : Array (Array Nat) := #[]
  for g in gs do
    let mut t : Array Nat := #[]
    for i in [0:N] do
      match pos.get? g[R[i]!]! with
      | some j => t := t.push j
      | none => throwError "#kc_orbrec: the points are not closed under the arrays"
    tabs := tabs.push t
  if N < 3 || k == 0 || k > gs.size then throwError "#kc_orbrec: {N} points, {k} steps"
  let mut D : Array Nat := Array.replicate N 0
  let mut c := 3
  for h in [0:N] do
    if h < c then
      for j in [0:k] do
        let q := tabs[j]![h]!
        if q == c then
          D := D.set! c (k * h + j)
          c := c + 1
        else if q > c then throwError "#kc_orbrec: the points are not in breadth-first order"
  if c != N then throwError "#kc_orbrec: the closure has {c} of the {N} points"
  let S := (Array.range N).qsort fun a b => R[a]! < R[b]!
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `N) natT (lit N)
    addTree (P ++ `T) R
    addTree (P ++ `S) S
    addTree (P ++ `D) D
    addTree (P ++ `G) (tabs.map (pack w))

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kc_nattree " pre:ident cId:ident : command => do
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let c ← liftTermElabM <| unsafe evalConst (Array Nat) cN
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree pre.getId c

end
