module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.RankThree.Native.PermEnumeration
public import Certificates.Kernel.Sporadic.RawGen
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kh_tree " pre:ident cId:ident nn:num psId:ident : command => do
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let c ← liftTermElabM <| unsafe evalConst CFSG.Monster.B.Fischer.ArrCert cN
  let psN ← liftCoreM <| realizeGlobalConstNoOverload psId
  let ps ← liftTermElabM <| unsafe evalConst (List Nat) psN
  let n := nn.getNat
  let P := pre.getId
  let N := c.pts.size
  let keys := c.pts.map (CFSG.RankThree.Native.keyA n ps)
  let sk := (Array.range N).qsort fun a b => keys[a]! < keys[b]!
  let ski := Id.run do
    let mut r := Array.replicate N 0
    for j in [0:N] do
      r := r.set! sk[j]! j
    return r
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `ER) (c.edges.map (pack 16))
    addTree (P ++ `P) c.par
    addTree (P ++ `L) c.lab
    addTree (P ++ `SK) sk
    addTree (P ++ `SKI) ski
    addDef (P ++ `N) natT (lit N)

end
