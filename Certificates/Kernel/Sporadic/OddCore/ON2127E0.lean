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

#kpenum CertificateChecks.KernelSpor.ON2127.R0 240 8 false CertificateChecks.KernelSpor.ON2127.g0
  CertificateChecks.KernelSpor.ON2127.g0 CertificateChecks.KernelSpor.ON2127.id240 50000
#kpenum CertificateChecks.KernelSpor.ON2127.R1 240 8 false CertificateChecks.KernelSpor.ON2127.g1
  CertificateChecks.KernelSpor.ON2127.g1 CertificateChecks.KernelSpor.ON2127.id240 50000

namespace CertificateChecks.KernelSpor.ON2127

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PEnumL

@[expose] noncomputable def sl0 (s : Nat) : Bool :=
  penumSlL 240 8 (mask 8) R0.G R0.k R0.cnt R0.T R0.PL R0.POS R0.SRT R0.SRI (Nat.mul s 2016) 2016

@[expose] noncomputable def sl1 (s : Nat) : Bool :=
  penumSlL 240 8 (mask 8) R1.G R1.k R1.cnt R1.T R1.PL R1.POS R1.SRT R1.SRI (Nat.mul s 2016) 2016

end CertificateChecks.KernelSpor.ON2127

#kon_slices CertificateChecks.KernelSpor.ON2127.sl0 0 20
#kon_join CertificateChecks.KernelSpor.ON2127.sl0All CertificateChecks.KernelSpor.ON2127.sl0 20
#kon_slices CertificateChecks.KernelSpor.ON2127.sl1 0 20
#kon_join CertificateChecks.KernelSpor.ON2127.sl1All CertificateChecks.KernelSpor.ON2127.sl1 20

end
