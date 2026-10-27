module

public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step44Data
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step44Tests
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaTests
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

namespace CertificateChecks.KernelLC.Step44Enum

open CFSG.ComponentClassification.AS81.Hexa

meta def wGens : List (Array Nat) := [hexaOmega, hexaMu]

end CertificateChecks.KernelLC.Step44Enum

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.S44K CFSG.ComponentClassification.AS81.Hexa.k36Gens 64 7
#lc_bfs CertificateChecks.KernelLC.S44W CertificateChecks.KernelLC.Step44Enum.wGens 64 7
#lc_bfs CertificateChecks.KernelLC.S44H CFSG.ComponentClassification.AS81.Hexa.hexaNormGens 64 7
#lc_bfs CertificateChecks.KernelLC.S44N CFSG.ComponentClassification.AS81.Hexa.hexaNGens 256 9
#lc_bfs CertificateChecks.KernelLC.S44E CFSG.ComponentClassification.AS81.Hexa.hexaNEGens 256 9
#lc_bfs CertificateChecks.KernelLC.S44P CFSG.ComponentClassification.AS81.Hexa.hexaPGens 256 9
#lc_bfs CertificateChecks.KernelLC.S44Q CFSG.ComponentClassification.AS81.Hexa.hexaPEGens 256 9
#lc_bfs CertificateChecks.KernelLC.S44L CFSG.ComponentClassification.AS81.Hexa.smLamGens 256 9
#lc_bfs CertificateChecks.KernelLC.S44Ab CFSG.ComponentClassification.AS81.Hexa.hexaAbImgs 32 6
#lc_bfs CertificateChecks.KernelLC.S44Aa CFSG.ComponentClassification.AS81.Hexa.hexaAaImgs 16 5

end
