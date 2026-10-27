module

public import Certificates.Kernel.Sporadic.ON5.Data
public meta import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporONCheckInputs
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

namespace CertificateChecks.KernelSpor.ONKL

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native
  CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK

meta def yPM : List Nat := [CFSG.KS.RawGen.pack 7 onKY5, CFSG.KS.RawGen.pack 7 onKY7]

meta def centM (y : Array Nat) : List Nat :=
  (List.range m120Enum.tabs.size).filter fun i =>
    comp 120 m120Enum.tabs[i]! y == comp 120 y m120Enum.tabs[i]!

meta def yPosM : List Nat :=
  [onKY5, onKY7].map fun y => ((List.range m120Enum.tabs.size).find? fun i =>
    m120Enum.tabs[i]! == y).getD 0

meta def c5M : List Nat := centM onKY5

meta def c7M : List Nat := centM onKY7

meta def dPM : List Nat := onKD.toList.map (CFSG.KS.RawGen.pack 6)

meta def ezPM : List Nat := [CFSG.KS.RawGen.pack 6 onKE, CFSG.KS.RawGen.pack 6 Data.T32z]

meta def ePosM : List Nat :=
  (List.range t32Enum.tabs.size).filter fun i => t32Enum.tabs[i]! == onKE

end CertificateChecks.KernelSpor.ONKL

#knatlist CertificateChecks.KernelSpor.ONKL.yP CertificateChecks.KernelSpor.ONKL.yPM
#knatlist CertificateChecks.KernelSpor.ONKL.yPos CertificateChecks.KernelSpor.ONKL.yPosM
#knatlist CertificateChecks.KernelSpor.ONKL.c5 CertificateChecks.KernelSpor.ONKL.c5M
#knatlist CertificateChecks.KernelSpor.ONKL.c7 CertificateChecks.KernelSpor.ONKL.c7M
#knatlist CertificateChecks.KernelSpor.ONKL.dP CertificateChecks.KernelSpor.ONKL.dPM
#knatlist CertificateChecks.KernelSpor.ONKL.ezP CertificateChecks.KernelSpor.ONKL.ezPM
#knatlist CertificateChecks.KernelSpor.ONKL.ePos CertificateChecks.KernelSpor.ONKL.ePosM

end
