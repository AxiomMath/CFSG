module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import CFSG.Sporadic.ONOddCore.QuotOuterCheckInputs
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

namespace CertificateChecks.KernelSpor.ON2127

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ONOddCore

meta def qpM : Array (Array Nat) :=
  #[qgArr 0, qgArr 1, Data.quotientConjugator, Data.M120Chain.generators[0]!,
    Data.M120Chain.generators[1]!] ++ Data.PSL120Chain.generators

meta def riM : Array (Array Nat) :=
  (localCert.records.toArray.map fun r => #[qiArr r 0, qiArr r 1]).flatten

meta def qIdxM : List Nat :=
  let idx := CFSG.PSL3Four.Native.indexOf m120Enum.tabs
  (riM.toList.map fun a => idx.getD (pcomp 120 (pinvCand 120 Data.quotientConjugator)
    (pcomp 120 a Data.quotientConjugator)) 0)

end CertificateChecks.KernelSpor.ON2127

#kmisc_packarrs CertificateChecks.KernelSpor.ON2127.QP CertificateChecks.KernelSpor.ON2127.qpM 7
#kmisc_packarrs CertificateChecks.KernelSpor.ON2127.RI CertificateChecks.KernelSpor.ON2127.riM 7
#knatlist CertificateChecks.KernelSpor.ON2127.qIdx CertificateChecks.KernelSpor.ON2127.qIdxM

end
