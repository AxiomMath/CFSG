module

public meta import CFSG.Quasithin.Background.G2UTables
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

namespace CFSG.KC.Misc.G2UGen

open CFSG.Quasithin.G2U

meta def packL (w : Nat) (m : List Nat) : Nat :=
  m.foldr (fun r acc => r ||| (acc <<< w)) 0

meta def codeR (c : List Nat) : Nat := packL 14 c

meta def codeD (c : List Nat) : Nat := packL 4 (c.take 9) + 2 ^ 36 * packL 14 (c.drop 9)

meta def parL (par : List (Nat × Nat)) : List Nat :=
  0 :: par.map fun ps => ps.1 + 2 ^ 24 * ps.2

meta def sortL (E : Array Nat) : List Nat :=
  ((Array.range E.size).qsort fun a b => E[a]! < E[b]!).toList

meta def closL (code : List Nat → Nat) (mul : List Nat → List Nat → List Nat)
    (gens : List (List Nat)) (es : Array (List Nat)) : List Nat :=
  let E := es.map code
  let idx : Std.HashMap Nat Nat := (List.range E.size).foldl (fun m t => m.insert E[t]! t) {}
  (List.range es.size).flatMap fun k => gens.map fun g => idx.getD (code (mul es[k]! g)) 0

meta def rE : List Nat := elemsR.toList.map codeR
meta def rG : List Nat := gensR.map codeR
meta def rP : List Nat := parL parR
meta def rS : List Nat := sortL (elemsR.map codeR)
meta def rC : List Nat := closL codeR mul2 gensR elemsR

meta def dE : List Nat := elemsD.toList.map codeD
meta def dG : List Nat := gensD.map codeD
meta def dP : List Nat := parL parD
meta def dS : List Nat := sortL (elemsD.map codeD)
meta def dC : List Nat := closL codeD mulP gensD elemsD

end CFSG.KC.Misc.G2UGen

end
