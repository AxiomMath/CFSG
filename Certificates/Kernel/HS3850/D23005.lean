module

public import Certificates.Kernel.LocalQT.PEnumD
public meta import Certificates.Data.GSThmBCatalog5CovHS
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

namespace CFSG.KD.HS3850.D23005

meta def c4M : Array (Array Nat) := CFSG.ComponentClassification.GSThmB.CovHS.c4Tabs

meta def qM : Array (Array Nat) := CFSG.ComponentClassification.GSThmB.CovHS.qGens

meta def idM : Array Nat := CFSG.PSL3Four.Native.idTab 3850

end CFSG.KD.HS3850.D23005

#kpenum_d CFSG.KD.HS3850.EC 3850 12 false CFSG.KD.HS3850.D23005.c4M CFSG.KD.HS3850.D23005.c4M
  CFSG.KD.HS3850.D23005.idM 1920
#kpenum_d CFSG.KD.HS3850.EQ 3850 12 false CFSG.KD.HS3850.D23005.qM CFSG.KD.HS3850.D23005.qM
  CFSG.KD.HS3850.D23005.idM 16

end
