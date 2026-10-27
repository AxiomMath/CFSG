module

public import Certificates.Kernel.LocalComp.L34Gen2
public meta import Certificates.Kernel.LocalComp.L34Gen2
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicCertInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
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

namespace CertificateChecks.KernelLC.L34IdxGen

open CFSG.PSL3Four.Native CertificateChecks.KernelLC.L34Gen
open CFSG.ComponentClassification.GrSLit.L34Facts

meta def pow4 (x : Array Nat) : Array Nat :=
  comp 42 (comp 42 (comp 42 x x) x) x

meta def t0Pts : Array (Array Nat) := (searchSt 4 (lst (wordTabs wT₀)) (idTab 42)).1

meta def cm (x y : Array Nat) : Bool := comp 42 x y == comp 42 y x

meta def yM : Array (Array Nat) :=
  let iS := posIn sPts
  let z5 := t0Pts[5]!
  let z51 := t0Pts[51]!
  rRun.1.filter fun y => cm y z5 && cm y z51 && pow4 y == idTab 42 && !iS.contains y

meta def wM : Array (Array Nat) :=
  let iS := posIn sPts
  chunks 16 ((Array.range (48 * 48)).map fun k =>
    let p := comp 42 yM[k / 48]! (invTab 42 yM[k % 48]!)
    if pow4 p == idTab 42 then iS.getD p 0 else 0)

meta def tsM : Array (Array Nat) :=
  let iS := posIn sPts
  chunks 16 (t0Pts.map fun t => iS.getD t 0)

end CertificateChecks.KernelLC.L34IdxGen

end
