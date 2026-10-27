module

public import Certificates.Kernel.U38Three.PGens
public import Certificates.Kernel.B3S3.Gen
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import Certificates.Kernel.U38Three.PGens
public meta import Certificates.Data.HuppertU38Three.Check
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

meta def pPtsM : Array (Array Nat) := (pCert ()).pts

meta def riM : List Nat := Id.run do
  let pts := pPtsM
  let mut reps : Array Nat := #[]
  for i in [0:pts.size] do
    let x := pts[i]!
    if !eqA 9 x (idA 9) then
      let met := pts.any fun g => reps.any fun r => eqA 9 (conjA 9 g x) pts[r]!
      if !met then
        reps := reps.push i
  return reps.toList

meta def chM : List Nat :=
  let pts := pPtsM
  let reps := riM
  (List.range pts.size).map fun i =>
    let x := pts[i]!
    if eqA 9 x (idA 9) then 0 else
      ((List.range pts.size).find? fun h =>
        reps.any fun r => eqA 9 (conjA 9 pts[h]! x) pts[r]!).getD 0

meta def qGensM (k : Nat) : Array (Array Nat) := conjGensM 9 12 (pCert ()) (riM.getD k 0)

meta def qG0 : Array (Array Nat) := qGensM 0
meta def qG1 : Array (Array Nat) := qGensM 1
meta def qG2 : Array (Array Nat) := qGensM 2
meta def qG3 : Array (Array Nat) := qGensM 3
meta def qG4 : Array (Array Nat) := qGensM 4
meta def qG5 : Array (Array Nat) := qGensM 5
meta def qG6 : Array (Array Nat) := qGensM 6
meta def qG7 : Array (Array Nat) := qGensM 7

end CertificateChecks.KernelU38Three

end

set_option maxRecDepth 400000

#kb3_enum CertificateChecks.KernelU38Three.PE CertificateChecks.KernelU38Three.pGens
  CertificateChecks.KernelU38Three.pBase 9 4
#knatlist CertificateChecks.KernelU38Three.RI CertificateChecks.KernelU38Three.riM
#knatlist CertificateChecks.KernelU38Three.CH CertificateChecks.KernelU38Three.chM
#kb3_enum CertificateChecks.KernelU38Three.Q0 CertificateChecks.KernelU38Three.qG0
  CertificateChecks.KernelU38Three.pBase 9 4
#kb3_enum CertificateChecks.KernelU38Three.Q1 CertificateChecks.KernelU38Three.qG1
  CertificateChecks.KernelU38Three.pBase 9 4
#kb3_enum CertificateChecks.KernelU38Three.Q2 CertificateChecks.KernelU38Three.qG2
  CertificateChecks.KernelU38Three.pBase 9 4
#kb3_enum CertificateChecks.KernelU38Three.Q3 CertificateChecks.KernelU38Three.qG3
  CertificateChecks.KernelU38Three.pBase 9 4
#kb3_enum CertificateChecks.KernelU38Three.Q4 CertificateChecks.KernelU38Three.qG4
  CertificateChecks.KernelU38Three.pBase 9 4
#kb3_enum CertificateChecks.KernelU38Three.Q5 CertificateChecks.KernelU38Three.qG5
  CertificateChecks.KernelU38Three.pBase 9 4
#kb3_enum CertificateChecks.KernelU38Three.Q6 CertificateChecks.KernelU38Three.qG6
  CertificateChecks.KernelU38Three.pBase 9 4
#kb3_enum CertificateChecks.KernelU38Three.Q7 CertificateChecks.KernelU38Three.qG7
  CertificateChecks.KernelU38Three.pBase 9 4
