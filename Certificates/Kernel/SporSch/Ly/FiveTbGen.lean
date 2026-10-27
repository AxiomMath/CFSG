module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.RankThree.Native.LyFiveImagesInputs
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

namespace CertificateChecks.KernelSporSch.LyFiveTbGen

open CFSG.KC.Eval CFSG.RankThree.Native

meta def keyOf (x : Array (ZMod 5)) : Nat :=
  (List.range 16).foldr (fun t acc => (x[t]!).val + 8 * acc) 0

public meta def tbStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "tbStep: expected no arguments"
  let arr := lyFiveTbArr
  if arr.size != 2880 then throw "tbStep: expected 2880 images"
  let keys := arr.map keyOf
  let so := (Array.range 2880).qsort fun a b => keys[a]! < keys[b]!
  let mut ks := 0
  let mut sk := 0
  let mut rho := 0
  for k in [0:2880] do
    ks := ks ||| (keys[k]! <<< (48 * k))
    sk := sk ||| (keys[so[k]!]! <<< (48 * k))
    rho := rho ||| (so[k]! <<< (12 * k))
  return #[(`G0, .nat (keyOf (fiveArr4 lyFiveAbar))), (`G1, .nat (keyOf (fiveArr4 lyFiveBbar))),
    (`KS, .nat ks), (`SK, .nat sk), (`RHO, .nat rho)]

end CertificateChecks.KernelSporSch.LyFiveTbGen
