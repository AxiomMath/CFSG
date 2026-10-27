module

public import Certificates.Data.Kernel.G28.R2
public import Certificates.Data.Kernel.Misc.PermClos
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Co1B.GenTri2045
public meta import Certificates.Kernel.G28.R9549Gen
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

#kss_natlist CertificateChecks.KernelG28.R9549.RE CFSG.KC.G28RGen.eL
#kss_natlist CertificateChecks.KernelG28.R9549.RG CFSG.KC.G28RGen.gL
#kss_natlist CertificateChecks.KernelG28.R9549.RP CFSG.KC.G28RGen.pL
#kss_natlist CertificateChecks.KernelG28.R9549.RC CFSG.KC.G28RGen.cL
#kss_natlist CertificateChecks.KernelG28.R9549.RI CFSG.KC.G28RGen.iL
#kss_natlist CertificateChecks.KernelG28.R9549.RT CFSG.KC.G28RGen.tL
#kss_natlist CertificateChecks.KernelG28.R9549.RCC CFSG.KC.G28RGen.ccL
#kss_natlist CertificateChecks.KernelG28.R9549.RW CFSG.KC.G28RGen.wL

namespace CertificateChecks.KernelG28.R9549

open CFSG.KC.G28R CFSG.KC.Misc.Clos

@[expose] noncomputable def r9549T (q : Nat) : Bool :=
  allR (Nat.mul 1008 q) 1008 (treeAt m2K idK RG 4 RE RP)

@[expose] noncomputable def r9549C (q : Nat) : Bool :=
  allR (Nat.mul 252 q) 252 (closedAt m2K RG 4 12096 RE RC)

@[expose] noncomputable def r9549E (q : Nat) : Bool :=
  allR (Nat.mul 168 q) 168 (elemAt RE RW RI RT 12096)

@[expose] noncomputable def r9549R (q : Nat) : Bool := repAt RI RT RCC q

end CertificateChecks.KernelG28.R9549

#kc_slices CertificateChecks.KernelG28.R9549.TK CertificateChecks.KernelG28.R9549.r9549T 12
#kc_slices CertificateChecks.KernelG28.R9549.CK CertificateChecks.KernelG28.R9549.r9549C 48
#kc_slices CertificateChecks.KernelG28.R9549.EK CertificateChecks.KernelG28.R9549.r9549E 72
#kc_slices CertificateChecks.KernelG28.R9549.RK CertificateChecks.KernelG28.R9549.r9549R 2

end
