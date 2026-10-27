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

#kpenum CertificateChecks.KernelSpor.ON2127.R4 240 8 false CertificateChecks.KernelSpor.ON2127.g4
  CertificateChecks.KernelSpor.ON2127.g4 CertificateChecks.KernelSpor.ON2127.id240 50000
#kpenum CertificateChecks.KernelSpor.ON2127.R5 240 8 false CertificateChecks.KernelSpor.ON2127.g5
  CertificateChecks.KernelSpor.ON2127.g5 CertificateChecks.KernelSpor.ON2127.id240 50000

namespace CertificateChecks.KernelSpor.ON2127

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PEnumL

@[expose] noncomputable def sl4 (s : Nat) : Bool :=
  penumSlL 240 8 (mask 8) R4.G R4.k R4.cnt R4.T R4.PL R4.POS R4.SRT R4.SRI (Nat.mul s 2016) 2016

@[expose] noncomputable def sl5 (s : Nat) : Bool :=
  penumSlL 240 8 (mask 8) R5.G R5.k R5.cnt R5.T R5.PL R5.POS R5.SRT R5.SRI (Nat.mul s 2016) 2016

end CertificateChecks.KernelSpor.ON2127

#kon_slices CertificateChecks.KernelSpor.ON2127.sl4 0 20
#kon_join CertificateChecks.KernelSpor.ON2127.sl4All CertificateChecks.KernelSpor.ON2127.sl4 20
#kon_slices CertificateChecks.KernelSpor.ON2127.sl5 0 20
#kon_join CertificateChecks.KernelSpor.ON2127.sl5All CertificateChecks.KernelSpor.ON2127.sl5 20

end
