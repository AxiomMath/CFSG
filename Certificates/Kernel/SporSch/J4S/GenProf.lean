module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Sporadic.Schreier.J4SData

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.Sporadic.J4Schreier in
elab "#kss_prof11 " pre:ident : command => do
  let E ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) ``elementColumns
  let SQ ← liftTermElabM <| unsafe evalConst (Array Nat) ``squares
  let CT ← liftTermElabM <| unsafe evalConst (Array Nat) ``cTable
  let app := fun (C : Array Nat) (a : Nat) => Id.run do
    let mut r := 0
    for j in [0:11] do
      if (a >>> j) % 2 == 1 then r := r ^^^ C[j]!
    return r
  let ell := fun (n : Nat) => Id.run do
    let mut r := 0
    for j in [0:11] do
      r := r ^^^ (((n &&& 300) >>> j) % 2)
    return r
  let kf := fun (n0 e0 : Nat) => Id.run do
    let mut n := n0
    let mut e := e0
    for m in [0:5] do
      if n == 0 && e == 0 then return m
      n := n ^^^ app E[e]! n
      e := SQ[e]!
    return 5
  let mut S : Array Nat := #[]
  for s in [0:128] do
    let mut acc := 0
    for e in [8 * s:8 * s + 8] do
      for n in [0:2048] do
        acc := acc + (1 <<< (24 * (6 * (ell n + 2 * CT[e]!) + kf n e)))
    S := S.push acc
  let S' := S
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree pre.getId S'

end
