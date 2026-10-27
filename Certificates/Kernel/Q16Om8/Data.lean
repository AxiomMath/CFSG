module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Sporadic.OrbRecGen
public import CFSG.Certificates.Kernel.Common.Eval
public import Certificates.Data.Kernel.Q16BK
meta import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Kernel.LocalComp.Q16Wit
meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
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

namespace CertificateChecks.KernelQ16Om8.E

open CFSG.EvenSmallLie.OmegaEight CFSG.KC.Q16Wit

meta def gQ : List (Array Nat) := [0, 2, 4, 6].map fun i => copy0Arr genArrs[i]!

meta def wQ : Array (Array Nat) := q16Trees 120 7 gQ [0, 8, 24]
meta def qSKT : Array Nat := wQ[0]!
meta def qRI : Array Nat := wQ[1]!
meta def qC : Array Nat := wQ[2]!
meta def qW : Array Nat := wQ[3]!
meta def qStep : CFSG.KC.Eval.Step := q16Step 120 7 gQ [0, 8, 24]

end CertificateChecks.KernelQ16Om8.E

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelQ16Om8.CS CertificateChecks.KernelQ16Om8.E.gQ 120 7
#kc_eval CertificateChecks.KernelQ16Om8 CS CertificateChecks.KernelQ16Om8.E.qStep
#kc_nattree CertificateChecks.KernelQ16Om8.CS.SKT CertificateChecks.KernelQ16Om8.E.qSKT
#kc_nattree CertificateChecks.KernelQ16Om8.CS.RI CertificateChecks.KernelQ16Om8.E.qRI
#kc_nattree CertificateChecks.KernelQ16Om8.CS.C CertificateChecks.KernelQ16Om8.E.qC
#kc_nattree CertificateChecks.KernelQ16Om8.CS.W CertificateChecks.KernelQ16Om8.E.qW

end
