module

public import Certificates.Kernel.LocalComp.L34Gen2
public meta import Certificates.Kernel.LocalComp.L34Gen2
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L34CertInputs
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

namespace CertificateChecks.KernelLC.L34CosGen

open CFSG.PSL3Four.Native CertificateChecks.KernelLC.L34Gen
open CFSG.ComponentClassification.CatFactsL4U4

meta def cstS (k : Nat) (t : Array Nat) : Array Nat :=
  comp 42 (comp 42 gensS[k]! t) (invTab 42 gensS[k]!)

meta def oS (i : Nat) : Array (Array Nat) × Array (Array Nat) := searchSt 3 cstS repT[i]!

meta def oLayS (i : Nat) := let o := oS i; layout o.1 o.2 11 o.1.size

meta def oCT (i : Nat) : Array (Array Nat) := (oLayS i).1
meta def oCE (i : Nat) : Array (Array Nat) := (oLayS i).2.1
meta def oCS (i : Nat) : Array (Array Nat) := (oLayS i).2.2.1
meta def oCSI (i : Nat) : Array (Array Nat) := (oLayS i).2.2.2.1

meta def t0 := oCT 0
meta def t1 := oCT 1
meta def t2 := oCT 2
meta def t3 := oCT 3
meta def t4 := oCT 4
meta def t5 := oCT 5
meta def t6 := oCT 6
meta def t7 := oCT 7
meta def e0 := oCE 0
meta def e1 := oCE 1
meta def e2 := oCE 2
meta def e3 := oCE 3
meta def e4 := oCE 4
meta def e5 := oCE 5
meta def e6 := oCE 6
meta def e7 := oCE 7
meta def s0 := oCS 0
meta def s1 := oCS 1
meta def s2 := oCS 2
meta def s3 := oCS 3
meta def s4 := oCS 4
meta def s5 := oCS 5
meta def s6 := oCS 6
meta def s7 := oCS 7
meta def si0 := oCSI 0
meta def si1 := oCSI 1
meta def si2 := oCSI 2
meta def si3 := oCSI 3
meta def si4 := oCSI 4
meta def si5 := oCSI 5
meta def si6 := oCSI 6
meta def si7 := oCSI 7

meta def repP : Array (Array Nat) := ones repT

meta def covW (o : Nat) : Array (Array Nat) :=
  let maps := (Array.range 8).map fun s => posIn (oS s).1
  chunks 16 ((oPts o).map fun x =>
    ((Array.range 8).findSome? fun s => (maps[s]!.get? x).map (s * 512 + ·)).getD 0)

meta def w0 := covW 0
meta def w1 := covW 1
meta def w2 := covW 2
meta def w3 := covW 3

end CertificateChecks.KernelLC.L34CosGen

end
