
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

meta def orbVals : Array Nat := CFSG.Sporadic.ThSchreier.orbTable.map packM

meta def orbSo : Array Nat := (Array.range orbVals.size).qsort fun a b => orbVals[a]! < orbVals[b]!

meta def sortedL : List Nat := (orbSo.map fun i => orbVals[i]!).toList

meta def sgL : List Nat := Id.run do
  let mut r := Array.replicate orbSo.size 0
  for k in [0:orbSo.size] do
    r := r.set! orbSo[k]! k
  return r.toList

meta def soL : List Nat := orbSo.toList

end CFSG.KS.SporSchGen

end
