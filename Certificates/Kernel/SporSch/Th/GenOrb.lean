
module

public meta import Lean
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819Inputs
public import Certificates.Data.Kernel.SporSch.ThOrb
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KS.SporSchGen

open CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier

meta def v4Nat (v : V4) : Nat :=
  v.w0.toNat ||| (v.w1.toNat <<< 64) ||| (v.w2.toNat <<< 128) ||| (v.w3.toNat <<< 192)

meta def packM (a : Array V4) : Nat := Id.run do
  let mut acc := 0
  for i in [0:a.size] do
    acc := acc ||| (v4Nat a[i]! <<< (256 * i))
  return acc

meta def matsL : List Nat :=
  let rB := CFSG.Sporadic.Th.Max3.rowsB
  let rY := CFSG.Sporadic.ThSchreier.rowsLY
  [packM CFSG.Sporadic.Th.Max3.rowsA, packM rB, packM (mulRows rB rB),
    packM CFSG.Sporadic.ThSchreier.rowsLX, packM rY, packM (mulRows rY rY),
    packM CFSG.Sporadic.ThSchreier.rowsV, packM CFSG.Sporadic.ThSchreier.rowsVInv,
    packM CFSG.Sporadic.ThSchreier.rowsT]

meta def thCcN : Nat := (2 ^ 63488 - 1) / (2 ^ 256 - 1)

meta def thBcL (M : Nat) : List Nat :=
  (List.range 248).map fun k => ((M >>> k) &&& thCcN) * (2 ^ 248 - 1)

meta def thBcR (M : Nat) : List Nat :=
  (List.range 248).map fun k => ((M >>> (256 * k)) &&& (2 ^ 248 - 1)) * thCcN

meta def thMulB (left : Bool) (C R : Array Nat) (A B : Nat) : Nat := Id.run do
  let cc := thCcN
  let rm := 2 ^ 248 - 1
  let mut acc := 0
  for k in [0:248] do
    acc := acc ^^^ (if left then C[k]! &&& (((B >>> (256 * k)) &&& rm) * cc)
      else (((A >>> k) &&& cc) * rm) &&& R[k]!)
  return acc

meta def orbVals : Array Nat := Id.run do
  let M := matsL.toArray
  let xc := (thBcL M[3]!).toArray
  let xr := (thBcR M[3]!).toArray
  let yc := (thBcL M[4]!).toArray
  let yyr := (thBcR M[5]!).toArray
  let mut out : Array Nat := #[M[8]!]
  for i in [1:819] do
    let m := out[orbPar i]!
    out := out.push (if orbLab i == 1 then thMulB false #[] xr (thMulB true xc #[] 0 m) 0
      else thMulB false #[] yyr (thMulB true yc #[] 0 m) 0)
  return out

meta def thOrbL : List Nat := Id.run do
  let vals := orbVals
  let so := (Array.range vals.size).qsort fun a b => vals[a]! < vals[b]!
  let mut sg := Array.replicate so.size 0
  for k in [0:so.size] do
    sg := sg.set! so[k]! k
  return (so.map fun i => vals[i]!).toList ++ sg.toList ++ so.toList

end CFSG.KS.SporSchGen

end
