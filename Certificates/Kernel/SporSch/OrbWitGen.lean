module

public import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public import Lean.Exception

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#ks_orbwit " pre:ident nn:num ww:num gId:ident oId:ident : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let oN ← liftCoreM <| realizeGlobalConstNoOverload oId
  let G ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let O ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) oN
  let cat := O.foldl (· ++ ·) #[]
  unless cat.size == n do throwError "#ks_orbwit: the lists have {cat.size} points, expected {n}"
  let opi := inv n cat
  let mut wp : Array Nat := Array.replicate n 0
  let mut wg : Array Nat := Array.replicate n 0
  let mut wd : Array Nat := Array.replicate n 0
  let mut seen : Array Bool := Array.replicate n false
  for o in O do
    let root := o[0]!
    seen := seen.set! root true
    let mut q : Array Nat := #[root]
    let mut h := 0
    while h < q.size do
      let x := q[h]!
      for j in [0:G.size] do
        let y := (G[j]!)[x]!
        if !seen[y]! then
          seen := seen.set! y true
          wp := wp.set! y x
          wg := wg.set! y j
          wd := wd.set! y (wd[x]! + 1)
          q := q.push y
      h := h + 1
    unless q.size == o.size do
      throwError "#ks_orbwit: a list of {o.size} points reaches {q.size} points"
  withSync do
    addDef (P ++ `OPI) natT (lit (pack w opi))
    addDef (P ++ `WP) natT (lit (pack w wp))
    addDef (P ++ `WG) natT (lit (pack w wg))
    addDef (P ++ `WD) natT (lit (pack w wd))
