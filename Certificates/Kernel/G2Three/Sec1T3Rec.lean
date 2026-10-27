module

public meta import Lean
meta import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Data.Kernel.G2Three.Sec1F
public import Certificates.Kernel.G2Three.Sec1T5Rec
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

namespace CFSG.KD.G2Three.Sec1T3.Gen

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

meta def bitsM (v : Nat) (l : List Nat) : Nat :=
  l.foldr (fun e acc => 2 * acc + if e == v then 1 else 0) 0

meta def pkM (m : List Nat) : Nat := 2 ^ 196 * bitsM 2 m + bitsM 1 m

meta def LOm : Nat := 2 ^ 196 - 1
meta def RMm : Nat := 2 ^ 14 - 1
meta def CIm : Nat := (List.range 14).foldl (fun a i => a ||| (1 <<< (14 * i))) 0
meta def LPm : Nat := 2 ^ 392 - 1
meta def LFm : Nat := 2 ^ 784 - 1

meta def mulM (A B : Nat) : Nat := Id.run do
  let A1 := A &&& LOm
  let A2 := A >>> 196
  let B1 := B &&& LOm
  let B2 := B >>> 196
  let mut x1 := 0
  let mut x2 := 0
  for k in [0:14] do
    let a1 := (A1 >>> k) &&& CIm
    let a2 := (A2 >>> k) &&& CIm
    let b1 := (B1 >>> (14 * k)) &&& RMm
    let b2 := (B2 >>> (14 * k)) &&& RMm
    let q := a1 * b1 + a2 * b2
    let m := a1 * b2 + a2 * b1
    let t := (x1 ||| m) ^^^ (x2 ||| q)
    let z1 := (x2 ||| m) ^^^ t
    let z2 := (x1 ||| q) ^^^ t
    x1 := z1
    x2 := z2
  return x1 + (x2 <<< 196)

meta def mp (a b : Nat) : Nat :=
  mulM (a &&& LPm) (b &&& LPm) + (mulM (a >>> 392) (b >>> 392) <<< 392)

meta def swp (a : Nat) : Nat := (a >>> 392) + ((a &&& LPm) <<< 392)

meta def mpF (a b : Nat) : Nat :=
  let f := a >>> 784
  let e := b &&& LFm
  mp (a &&& LFm) (if f == 1 then swp e else e) + ((f ^^^ (b >>> 784)) <<< 784)

meta def pr (a b : List Nat) : Nat := pkM a + (pkM b <<< 392)

meta def oneP : Nat := pr one14 one14
meta def gx0 : Nat := pr x0c x1c
meta def gx1 : Nat := pr x1c x0c
meta def gy0 : Nat := pr y0c y1c
meta def gy1 : Nat := pr y1c y0c
meta def n0 : Nat := mp (mp gx0 (mp gy0 gy0)) gx0
meta def n1 : Nat := mp (mp gx1 (mp gy1 gy1)) gx1
meta def n0i : Nat := mp (mp (mp gx0 gx0) gy0) (mp gx0 gx0)
meta def n1i : Nat := mp (mp (mp gx1 gx1) gy1) (mp gx1 gx1)
meta def u1 : Nat := mp (mp n0 gx1) n0i
meta def b1 : Nat := mp (mp n0 n1) n0i
meta def u2 : Nat := mp (mp n1 gx0) n1i
meta def b2 : Nat := mp (mp n1 n0) n1i
meta def h0 : Nat := mp n1 n1
meta def u1i : Nat := mp (mp n0 (mp gx1 gx1)) n0i
meta def u2i : Nat := mp (mp n1 (mp gx0 gx0)) n1i
meta def a1 : Nat := mp (mp u1 (mp b1 (mp b1 b1))) u1i
meta def a2 : Nat := mp (mp u2 (mp b2 (mp b2 b2))) u2i
meta def sig : Nat := oneP + (1 <<< 784)

meta def closM (one : Nat) (gens : List Nat) : Array Nat := Id.run do
  let gs := gens.toArray
  let mut es : Array Nat := #[one]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert one 0
  let mut h := 0
  while h < es.size do
    for s in [0:gs.size] do
      let y := mpF es[h]! gs[s]!
      if !idx.contains y then
        idx := idx.insert y es.size
        es := es.push y
    h := h + 1
  return es

meta def sortM (xs : Array Nat) : List Nat × List Nat :=
  let srt := (Array.range xs.size).qsort (fun a b => xs[a]! < xs[b]!)
  let sri := (Array.range srt.size).foldl (fun acc i => acc.set! srt[i]! i)
    (Array.replicate srt.size 0)
  (srt.toList, sri.toList)

meta def xA : Array Nat := closM oneP [a1, b1, a2, b2, h0, sig]
meta def xL : List Nat := xA.toList
meta def srtL : List Nat := (sortM xA).1
meta def sriL : List Nat := (sortM xA).2

end CFSG.KD.G2Three.Sec1T3.Gen

#kss_ntree CFSG.KD.G2Three.Sec1T3.X3 CFSG.KD.G2Three.Sec1T3.Gen.xL
#kss_ntree CFSG.KD.G2Three.Sec1T3.X3SRT CFSG.KD.G2Three.Sec1T3.Gen.srtL
#kss_ntree CFSG.KD.G2Three.Sec1T3.X3SRI CFSG.KD.G2Three.Sec1T3.Gen.sriL

public section

namespace CFSG.KD.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1

@[expose] noncomputable def gS3 (s : Nat) : Nat := nIf(Nat.blt s 5, Q5U s, SIGF)

end CFSG.KD.G2Three.Sec1T3

end
