module

public import Certificates.Kernel.U38Three.PGens
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Misc.Perm.CharsLits
public import Certificates.Kernel.B3S3.GenL
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import Certificates.Kernel.U38Three.PGens
public meta import Certificates.Data.HuppertU38Three.Check
public import Certificates.Data.HuppertU38.Data
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

namespace CertificateChecks.KernelU38Three

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native U38Three

meta def mwM : List Nat :=
  let pts := (lCert ()).pts
  let idx := fun (x : Array Nat) => ((List.range pts.size).find? fun i => eqA 513 pts[i]! x).getD 0
  (List.range 2).flatMap fun k => (List.range 2).flatMap fun x =>
    let y := lGens[x]!
    [idx (conjA 513 cGens[k]! y), idx (conjInvA 513 cGens[k]! y)]

end CertificateChecks.KernelU38Three

end

set_option maxRecDepth 400000

#ks_chars_lits CertificateChecks.KernelU38Three.FT U38Three.u3Hex
#kmisc_hexflat CertificateChecks.KernelU38Three.FT U38Three.u3Hex 3 513 10 7
#kb3_enum_l CertificateChecks.KernelU38Three.HE U38Three.hGens
  CFSG.RankThree.PartTwo.Sec4.Item434U38.base1 513 10
#kb3_enum_l CertificateChecks.KernelU38Three.LE CertificateChecks.KernelU38Three.lGens
  CFSG.RankThree.PartTwo.Sec4.Item434U38.base1 513 10
#kb3_enum_l CertificateChecks.KernelU38Three.CE U38Three.cGens
  CFSG.RankThree.PartTwo.Sec4.Item434U38.base1 513 10
#knatlist CertificateChecks.KernelU38Three.MW CertificateChecks.KernelU38Three.mwM
