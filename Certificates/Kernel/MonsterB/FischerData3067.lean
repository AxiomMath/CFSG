
module

public import CFSG.Certificates.Kernel.Spor.PackWord
meta import CFSG.Monster.B.TwoA.Fischer.CertSieveInputs
meta import CFSG.Monster.B.TwoA.Fischer.CertGramInputs
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

namespace CertificateChecks.KernelMonB.FD

open CFSG.Monster.B.TwoA.Fischer.Cert CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.SmallF2.Native

meta def pack (w : Nat) (L : List Nat) : Nat := L.foldr (fun x acc => x ||| (acc <<< w)) 0

meta def orbM : List Nat :=
  let d := orbitData
  [pack 11 d.1.toList, pack 11 d.2.1.toList, pack 11 d.2.2.1.toList, pack 11 d.2.2.2.toList]

meta def rowsM : List Nat := bTableArr.toList.map fun r => pack 78 r.toList

meta def invM : List Nat := (List.range 13).map fun k => pack 12 (invCand 3510 (indCandidate k)).toList

meta def lcM : List Nat := [pack 78 labelCoordArr.toList]

meta def gtM : List Nat := (transposeRows 78 gramRowArr).toList

end CertificateChecks.KernelMonB.FD

public section

#knatlist CertificateChecks.KernelMonB.FD.ORB CertificateChecks.KernelMonB.FD.orbM
#knatlist CertificateChecks.KernelMonB.FD.ROWS CertificateChecks.KernelMonB.FD.rowsM
#knatlist CertificateChecks.KernelMonB.FD.INV CertificateChecks.KernelMonB.FD.invM
#knatlist CertificateChecks.KernelMonB.FD.LC CertificateChecks.KernelMonB.FD.lcM
#knatlist CertificateChecks.KernelMonB.FD.GT CertificateChecks.KernelMonB.FD.gtM

end
