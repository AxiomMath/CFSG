module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowData
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowData
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheckInputs
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

namespace CertificateChecks.KernelLC.HeAutEnum

meta def yGens : List (Array Nat) :=
  CFSG.ComponentClassification.GrSLit.HeldFix.hfT0Tabs32.toList

end CertificateChecks.KernelLC.HeAutEnum

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.HeAutY CertificateChecks.KernelLC.HeAutEnum.yGens 32 6
#lc_bfs CertificateChecks.KernelLC.HeAutQ CFSG.ComponentClassification.AS81.HeSylow.heAutQ32 32 6
#lc_bfs CertificateChecks.KernelLC.HeAutE CFSG.ComponentClassification.AS81.HeSylow.heAutE32 32 6
#lc_bfs CertificateChecks.KernelLC.HeAutF CFSG.ComponentClassification.AS81.HeSylow.heAutF32 32 6
#lc_bfs CertificateChecks.KernelLC.HeAutU CFSG.ComponentClassification.AS81.HeSylow.heAutU32 32 6

end
