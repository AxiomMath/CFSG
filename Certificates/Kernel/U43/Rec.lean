module

public meta import Lean
meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43PairCheck
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
meta import Mathlib
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

namespace CFSG.KD.U43.Gen

open CFSG.RankThree.PartTwo.Sec4.Item434RemU43

meta def pkM (c : List Nat) : Nat := c.foldr (fun e acc => e + 16 * acc) 0

meta def xA : Array Nat := uElems.map pkM

meta def aL : List Nat := (List.range 4).map fun s => pkM (letterCode s)
meta def gL : List Nat := uGens.map pkM
meta def xL : List Nat := xA.toList

meta def sortM (xs : Array Nat) : List Nat × List Nat :=
  let srt := (Array.range xs.size).qsort (fun a b => xs[a]! < xs[b]!)
  let sri := (Array.range srt.size).foldl (fun acc i => acc.set! srt[i]! i)
    (Array.replicate srt.size 0)
  (srt.toList, sri.toList)

meta def srtL : List Nat := (sortM xA).1
meta def sriL : List Nat := (sortM xA).2

meta def posL : List Nat :=
  [(List.range 2187).foldl (fun acc i =>
    acc ||| (posOf (mul4 (uAt (i / 3)) (uGens.getD (i % 3) one4)) <<< (10 * i))) 0]

meta def kwL : List Nat :=
  (List.range 12).flatMap fun k =>
    (e9Elems (badA k) (badB k)).toList.map fun c => if c == one4 then 0 else posOf c

end CFSG.KD.U43.Gen

#kss_ntree CFSG.KD.U43.UA CFSG.KD.U43.Gen.aL
#kss_ntree CFSG.KD.U43.UG CFSG.KD.U43.Gen.gL
#kss_ntree CFSG.KD.U43.UX CFSG.KD.U43.Gen.xL
#kss_ntree CFSG.KD.U43.UPOS CFSG.KD.U43.Gen.posL
#kss_ntree CFSG.KD.U43.USRT CFSG.KD.U43.Gen.srtL
#kss_ntree CFSG.KD.U43.USRI CFSG.KD.U43.Gen.sriL
#kss_ntree CFSG.KD.U43.UKW CFSG.KD.U43.Gen.kwL
