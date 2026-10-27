module

public import Certificates.Data.Kernel.RouteP.RigidTwin
public import Certificates.Kernel.RouteP.Text.PlanesX
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

namespace CertificateChecks.KernelRouteP

open CFSG.KC.RouteP CFSG.KD.RouteP CFSG.KS.PK

@[expose] noncomputable def PGF (l x : Nat) : Nat := nIf(Nat.blt l (nat_lit 13), PGE l x, nat_lit 0)

@[expose] noncomputable def rgRun (r : Nat) : BS := BS.run PGF (List.range 13) 891 r

@[expose] noncomputable def rgRuns : List BS := [rgRun 0, rgRun 1, rgRun 12, rgRun 159]

@[expose] noncomputable def interK (a b : Nat) : Nat :=
  ((List.range 24).filter fun m => (List.range 24).any fun j => PXE b j == PXE a m).length

@[expose] def nodupB : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

@[expose] noncomputable def rgAll : Bool :=
  ((orbitBS PGF 13 891).map (fun s => s.pts.headD 0) == [0, 1, 12, 159]) &&
  (rgRuns.map (fun s => s.pts.length) == [1, 336, 512, 42]) &&
  ((List.range 891).all fun v => rgRuns.any fun s => s.pts.contains v) &&
  ((rgRun 0).pts.tail == []) &&
  ((rgRun 1).pts.tail.filter (candTw PGF 13 (rgRun 1)) == []) &&
  ((rgRun 12).pts.tail.filter (candTw PGF 13 (rgRun 12)) == []) &&
  ((rgRun 159).pts.tail.filter (candTw PGF 13 (rgRun 159)) == [590]) &&
  (interK (combinedTw PGF rgRuns [0, 1, 12, 590] 1) (combinedTw PGF rgRuns [0, 1, 12, 590] 588) !=
    interK 1 588) &&
  ((List.range 13).all fun s => nodupB ((List.range 891).map (PGE s)))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem rgAll_true : rgAll = true := by
  decide +kernel

end CertificateChecks.KernelRouteP
