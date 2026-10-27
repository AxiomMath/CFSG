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

namespace CFSG.KD.U43C.Gen

open CFSG.RankThree.PartTwo.Sec4.Item434RemU43

meta def fmM (c : List Nat) : Nat :=
  (List.range c.length).foldl (fun acc m =>
    acc + ((c.getD m 0 / 3) <<< (16 * m)) + ((c.getD m 0 % 3) <<< (256 + 16 * m))) 0

meta def sortM (xs : Array Nat) : List Nat × List Nat :=
  let srt := (Array.range xs.size).qsort (fun a b => xs[a]! < xs[b]!)
  let sri := (Array.range srt.size).foldl (fun acc i => acc.set! srt[i]! i)
    (Array.replicate srt.size 0)
  (srt.toList, sri.toList)

meta def aL : List Nat := (List.range 4).map fun s => fmM (letterCode s)
meta def gL : List Nat := uGens.map fmM
meta def xA : Array Nat := uElems.map fmM
meta def xL : List Nat := xA.toList
meta def srtL : List Nat := (sortM xA).1
meta def sriL : List Nat := (sortM xA).2

meta def gaL : List Nat := [fmM (wordCode [0]), fmM (wordCode [1])]
meta def gbL : List Nat := [fmM (wordCode (invWord [0])), fmM (wordCode (invWord [1]))]

meta def oA : Array (List Nat) := uOrbit
meta def oxA : Array Nat := oA.map fmM
meta def oxL : List Nat := oxA.toList
meta def osrtL : List Nat := (sortM oxA).1
meta def osriL : List Nat := (sortM oxA).2

meta def stepM : List Nat × List Nat := Id.run do
  let n := oA.size
  let idx : Std.HashMap (List Nat) Nat :=
    (List.range n).foldl (fun m t => m.insert oA[t]! t) {}
  let mut c := 1
  let mut wh : Array Nat := #[]
  let mut pp : Array Nat := Array.replicate (n - 1) 0
  for h in [0:n] do
    let x := oA[h]!
    let p0 := idx.getD (conjStep (orbGens.getD 0 []) x) n
    let p1 := idx.getD (conjStep (orbGens.getD 1 []) x) n
    wh := wh.push (c ||| (p0 <<< 16) ||| (p1 <<< 32))
    if p0 == c then
      pp := pp.set! (c - 1) (2 * h)
      c := c + 1
    if p1 == c then
      pp := pp.set! (c - 1) (2 * h + 1)
      c := c + 1
  wh := wh.push c
  return (wh.toList, pp.toList)

meta def owL : List Nat := stepM.1
meta def oppL : List Nat := stepM.2

meta def rtpL : List Nat := (List.range 81).map fun e => posOf (rtProd e)
meta def rtiL : List Nat :=
  ((List.range 81).foldl (fun acc e => acc.set! (rtpL.getD e 0) e) (Array.replicate 729 0)).toList

end CFSG.KD.U43C.Gen

#kss_ntree CFSG.KD.U43C.UAF CFSG.KD.U43C.Gen.aL
#kss_ntree CFSG.KD.U43C.UGF CFSG.KD.U43C.Gen.gL
#kss_ntree CFSG.KD.U43C.UXF CFSG.KD.U43C.Gen.xL
#kss_ntree CFSG.KD.U43C.USF CFSG.KD.U43C.Gen.srtL
#kss_ntree CFSG.KD.U43C.USIF CFSG.KD.U43C.Gen.sriL
#kss_ntree CFSG.KD.U43C.OGA CFSG.KD.U43C.Gen.gaL
#kss_ntree CFSG.KD.U43C.OGB CFSG.KD.U43C.Gen.gbL
#kss_ntree CFSG.KD.U43C.OX CFSG.KD.U43C.Gen.oxL
#kss_ntree CFSG.KD.U43C.OW CFSG.KD.U43C.Gen.owL
#kss_ntree CFSG.KD.U43C.OPP CFSG.KD.U43C.Gen.oppL
#kss_ntree CFSG.KD.U43C.OSRT CFSG.KD.U43C.Gen.osrtL
#kss_ntree CFSG.KD.U43C.OSRI CFSG.KD.U43C.Gen.osriL
#kss_ntree CFSG.KD.U43C.RTP CFSG.KD.U43C.Gen.rtpL
#kss_ntree CFSG.KD.U43C.RTI CFSG.KD.U43C.Gen.rtiL
