module

public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiInputs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

namespace CertificateChecks.KernelFi22Cover.GensM

meta def sM : Array (Array Nat) := CFSG.HardMathSupport.Solomon.Coordinator.fi22CoverS

meta def invM (a : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate a.size 0
  for i in [0:a.size] do
    r := r.set! a[i]! i
  return r

meta def siM : Array (Array Nat) := sM.map invM

end CertificateChecks.KernelFi22Cover.GensM

public section

#kmisc_packarrs CertificateChecks.KernelFi22Cover.S CertificateChecks.KernelFi22Cover.GensM.sM 12

#kmisc_packarrs CertificateChecks.KernelFi22Cover.SI CertificateChecks.KernelFi22Cover.GensM.siM 12

end
