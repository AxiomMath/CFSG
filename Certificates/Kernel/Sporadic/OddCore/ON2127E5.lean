module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Data.Kernel.Spor.PEnumL
public meta import Certificates.Kernel.Sporadic.OddCore.ON2127G
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

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelSpor.ON2127.R10 240 8 false CertificateChecks.KernelSpor.ON2127.g10
  CertificateChecks.KernelSpor.ON2127.g10 CertificateChecks.KernelSpor.ON2127.id240 50000
#kpenum CertificateChecks.KernelSpor.ON2127.R11 240 8 false CertificateChecks.KernelSpor.ON2127.g11
  CertificateChecks.KernelSpor.ON2127.g11 CertificateChecks.KernelSpor.ON2127.id240 50000

namespace CertificateChecks.KernelSpor.ON2127

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PEnumL

@[expose] noncomputable def slA (s : Nat) : Bool :=
  penumSlL 240 8 (mask 8) R10.G R10.k R10.cnt R10.T R10.PL R10.POS R10.SRT R10.SRI
    (Nat.mul s 2016) 2016

@[expose] noncomputable def slB (s : Nat) : Bool :=
  penumSlL 240 8 (mask 8) R11.G R11.k R11.cnt R11.T R11.PL R11.POS R11.SRT R11.SRI
    (Nat.mul s 2016) 2016

end CertificateChecks.KernelSpor.ON2127

#kon_slices CertificateChecks.KernelSpor.ON2127.slA 0 20
#kon_join CertificateChecks.KernelSpor.ON2127.slAAll CertificateChecks.KernelSpor.ON2127.slA 20
#kon_slices CertificateChecks.KernelSpor.ON2127.slB 0 20
#kon_join CertificateChecks.KernelSpor.ON2127.slBAll CertificateChecks.KernelSpor.ON2127.slB 20

end
