module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Monster.GMS.Griess13.DataPacked
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

namespace CertificateChecks.KernelG13

open CFSG.KC.Eval CFSG.Monster.GMS.Griess13.Co1Data

public meta def packRows (r : Array Nat) : Nat :=
  (List.range 24).foldl (fun acc i => acc + (r[i]?.getD 0 % 2 ^ 24) * 2 ^ (24 * i)) 0

public meta def packPR (p : PR) : Nat := packRows p.r + packRows p.s * 2 ^ 576

public meta def zig (e : Int) : Nat := if 0 ≤ e then 2 * e.toNat else 2 * (-e).toNat - 1

public meta def encFacts (fs : List (Nat × Int)) : Array Val :=
  (fs.flatMap fun f => [f.1, zig f.2]).toArray.map Val.nat

public meta def natL (xs : List Nat) : Val := .list (xs.toArray.map Val.nat)

public meta def stepG13 (_ : Array Val) : Except String (Array (Lean.Name × Val)) :=
  let p := parseSLP slpMax11
  .ok #[(`slpL, .list (p.lines.toArray.map fun l => .list (#[Val.nat l.1] ++ encFacts l.2))),
    (`slpO, .list (encFacts p.outs)),
    (`B2, .nat (packRows (CFSG.Sporadic.SmallF2.Native.mulRows 24 dat.rowsB dat.rowsB))),
    (`N1, .nat (packPR prN1)), (`N2, .nat (packPR prN2)),
    (`E, natL ((List.finRange 6).map fun i => packPR (prE i))),
    (`T, .nat (packPR prTau)),
    (`M, natL ((List.finRange 2).map fun i => packPR (prM i))),
    (`R, natL ((List.finRange 12).map fun k => packPR (prR k)))]

end CertificateChecks.KernelG13

end
