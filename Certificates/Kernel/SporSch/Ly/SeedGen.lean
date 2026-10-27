
module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.SporSch.Ly.GenLy
public meta import CFSG.RankThree.Native.LySeedCheckInputs
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

namespace CertificateChecks.KernelSporSch.LySeedGen

open CFSG.KC.Eval CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native CFSG.KS.SporSch.LyGen

meta def pEnt (j a : Nat) : Nat := if a < 7 then keyDigit rootKey (111 * a + j) else 0

meta def cEnt (a b : Nat) : Nat := if a < 7 && b < 7 then keyDigit rootKey (777 + 7 * a + b) else 0

meta def matOf (f : Nat → Nat → Nat) : Array (Array Nat) :=
  Array.ofFn (n := 111) fun i => Array.ofFn (n := 111) fun j => f i.val j.val

public meta def seedStep (args : Array Val) : Except String (Array (Lean.Name × Val)) :=
  if args.size != 0 then .error "seedStep: expected no arguments" else
  .ok #[(`F, .nat (packM formF)), (`FI, .nat (packM (invM 5 111 formF))),
    (`PL, .nat (packM (matOf pEnt))), (`PLT, .nat (packM (matOf fun a j => pEnt j a))),
    (`CL, .nat (packM (matOf cEnt)))]

end CertificateChecks.KernelSporSch.LySeedGen
