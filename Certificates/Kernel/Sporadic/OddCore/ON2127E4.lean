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

#kpenum CertificateChecks.KernelSpor.ON2127.R8 240 8 false CertificateChecks.KernelSpor.ON2127.g8
  CertificateChecks.KernelSpor.ON2127.g8 CertificateChecks.KernelSpor.ON2127.id240 50000
#kpenum CertificateChecks.KernelSpor.ON2127.R9 240 8 false CertificateChecks.KernelSpor.ON2127.g9
  CertificateChecks.KernelSpor.ON2127.g9 CertificateChecks.KernelSpor.ON2127.id240 50000

namespace CertificateChecks.KernelSpor.ON2127

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PEnumL

@[expose] noncomputable def sl8 (s : Nat) : Bool :=
  penumSlL 240 8 (mask 8) R8.G R8.k R8.cnt R8.T R8.PL R8.POS R8.SRT R8.SRI (Nat.mul s 2016) 2016

@[expose] noncomputable def sl9 (s : Nat) : Bool :=
  penumSlL 240 8 (mask 8) R9.G R9.k R9.cnt R9.T R9.PL R9.POS R9.SRT R9.SRI (Nat.mul s 2016) 2016

end CertificateChecks.KernelSpor.ON2127

#kon_slices CertificateChecks.KernelSpor.ON2127.sl8 0 20
#kon_join CertificateChecks.KernelSpor.ON2127.sl8All CertificateChecks.KernelSpor.ON2127.sl8 20
#kon_slices CertificateChecks.KernelSpor.ON2127.sl9 0 20
#kon_join CertificateChecks.KernelSpor.ON2127.sl9All CertificateChecks.KernelSpor.ON2127.sl9 20

end
