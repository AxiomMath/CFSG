module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_closure " pre:ident ww:num aId:ident bb:num : command => do
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let A ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) aN
  let P := pre.getId
  let w := ww.getNat
  let bound := bb.getNat
  let n := A[0]!.size
  let mut elts : Array (Array Nat) := #[Array.range n]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut head := 0
  for _ in [0:bound] do
    if head < elts.size && elts.size < bound then
      let e := elts[head]!
      for k in [0:A.size] do
        let t := comp n A[k]! e
        if elts.size < bound && !(elts.any (· == t)) then
          elts := elts.push t
          par := par.push head
          lab := lab.push k
      head := head + 1
  let PP := pack 16 par
  let LP := pack 8 lab
  let c := elts.size
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `E) (elts.map (pack w))
    addDef (P ++ `PP) natT (lit PP)
    addDef (P ++ `LP) natT (lit LP)
    addDef (P ++ `c) natT (lit c)

end
