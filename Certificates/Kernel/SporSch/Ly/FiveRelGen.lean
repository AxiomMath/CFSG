module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.SporSch.Ly.GenLy
public meta import CFSG.RankThree.Native.LyFiveCheckInputs
public import Certificates.Kernel.SporSch.Ly.GenLy
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

namespace CertificateChecks.KernelSporSch.LyFiveRelGen

open CFSG.KC.Eval CFSG.RankThree.Native CFSG.KS.SporSch.LyGen

meta def named (pre : String) (a : Array (Array (Array Nat))) : Array (Lean.Name × Val) :=
  (Array.range a.size).map fun k => (Lean.Name.mkSimple s!"{pre}{k}", .nat (packM a[k]!))

public meta def relStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "relStep: expected no arguments"
  let T := lyFiveTArr
  if T.size != 2880 then throw "relStep: expected 2880 lifts"
  let vp := (Array.range 4).foldl (fun acc i => acc ++ lyFiveVPow i) #[]
  return named "t" T ++ named "vp" vp ++ named "xp" lyFiveXPow ++ named "pa" lyFiveP32 ++
    named "pb" lyFiveP321 ++ named "pc" lyFiveP3210

end CertificateChecks.KernelSporSch.LyFiveRelGen
