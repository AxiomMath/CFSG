module

public meta import Lean
meta import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
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

namespace CFSG.KD.G2Three.Sec1.Gen2

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

meta def bitsM (v : Nat) (l : List Nat) : Nat :=
  l.foldr (fun e acc => 2 * acc + if e == v then 1 else 0) 0

meta def pkM (m : List Nat) : Nat := 2 ^ 196 * bitsM 2 m + bitsM 1 m

meta def LOm : Nat := 2 ^ 196 - 1
meta def RMm : Nat := 2 ^ 14 - 1
meta def CIm : Nat := (List.range 14).foldl (fun a i => a ||| (1 <<< (14 * i))) 0
meta def LPm : Nat := 2 ^ 392 - 1

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

meta def defs : List (Nat × Nat) :=
  [(0, 0), (1, 2), (3, 4), (1, 1), (5, 6), (1, 3), (5, 1), (14, 6), (5, 3), (1, 6), (2, 2),
    (8, 2), (19, 3), (0, 1), (21, 4), (22, 0), (11, 4), (5, 11), (1, 11), (6, 11), (3, 11),
    (12, 11), (13, 11), (15, 11), (0, 2), (0, 18), (8, 18), (6, 3), (35, 5)]

meta def uA : Array Nat :=
  defs.foldl (fun acc d => acc.push (mp acc[d.1]! acc[d.2]!)) #[u1, b1, u2, b2, h0, a1, a2, oneP]

meta def U (i : Nat) : Nat := uA[i]!

meta def closM (gens : List Nat) : Array Nat × Array (Nat × Nat) × Array Nat := Id.run do
  let gs := gens.toArray
  let mut es : Array Nat := #[oneP]
  let mut par : Array (Nat × Nat) := #[]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert oneP 0
  let mut h := 0
  while h < es.size do
    for s in [0:gs.size] do
      let y := mp es[h]! gs[s]!
      if !idx.contains y then
        idx := idx.insert y es.size
        es := es.push y
        par := par.push (h, s)
    h := h + 1
  let mut pos : Array Nat := #[]
  for e in es do
    for s in [0:gs.size] do
      pos := pos.push ((idx.get? (mp e gs[s]!)).getD 0)
  return (es, par, pos)

meta def sortM (xs : Array Nat) : List Nat × List Nat :=
  let srt := (Array.range xs.size).qsort (fun a b => xs[a]! < xs[b]!)
  let sri := (Array.range srt.size).foldl (fun acc i => acc.set! srt[i]! i)
    (Array.replicate srt.size 0)
  (srt.toList, sri.toList)

meta def find (xs : Array Nat) (x : Nat) : Nat :=
  ((List.range xs.size).find? fun i => xs[i]! == x).getD 0

meta def mem (xs : Array Nat) (x : Nat) : Bool := xs.contains x

meta def invM (x : Nat) : Nat := Id.run do
  let mut p := x
  for _ in [0:64] do
    let q := mp p x
    if q == oneP then return p
    p := q
  return oneP

meta def cj (g y : Nat) : Nat := mp (mp g y) (invM g)

meta def xH := (closM ([8, 9, 10].map U)).1
meta def gS : List Nat := [5, 1, 6, 3, 4]
meta def gB : List Nat := [1, 3, 4, 12]
meta def xS := (closM (gS.map U)).1
meta def cB := closM (gB.map U)
meta def xB := cB.1

meta def p4I : List Nat := [0, 0, 0, 1, 1, 2]
meta def p4J : List Nat := [1, 2, 3, 2, 3, 3]

meta def conjRec (T : Array Nat) (gs : List Nat) : List Nat × List Nat × List Nat := Id.run do
  let mut cs : List Nat := []
  let mut seen : List (List Nat) := []
  for i in [0:xH.size] do
    if cs.length < 4 then
      let key := ((T.toList.map fun t => cj xH[i]! t).toArray.qsort (· < ·)).toList
      if !(seen.contains key) then
        seen := seen ++ [key]
        cs := cs ++ [i]
  let ds := (List.range 6).map fun q =>
    find xH (mp (invM xH[cs[p4J[q]!]!]!) xH[cs[p4I[q]!]!]!)
  let ws := ds.map fun d =>
    ((List.range gs.length).find? fun w => !(mem T (cj xH[d]! (U gs[w]!)))).getD 0
  (cs, ds, ws)

meta def scR := conjRec xS gS
meta def bcR := conjRec xB gB
meta def scC := scR.1
meta def scD := scR.2.1
meta def scW := scR.2.2
meta def bcC := bcR.1
meta def bcD := bcR.2.1
meta def bcW := bcR.2.2
meta def xBL := xB.toList
meta def paB := cB.2.1.toList.map (·.1)
meta def pbB := cB.2.1.toList.map (·.2)
meta def posB := cB.2.2.toList
meta def srtB := (sortM xB).1
meta def sriB := (sortM xB).2

end CFSG.KD.G2Three.Sec1.Gen2

#kss_ntree CFSG.KD.G2Three.Sec1.R1BG CFSG.KD.G2Three.Sec1.Gen2.gB
#kss_ntree CFSG.KD.G2Three.Sec1.R1B CFSG.KD.G2Three.Sec1.Gen2.xBL
#kss_ntree CFSG.KD.G2Three.Sec1.R1BPA CFSG.KD.G2Three.Sec1.Gen2.paB
#kss_ntree CFSG.KD.G2Three.Sec1.R1BPB CFSG.KD.G2Three.Sec1.Gen2.pbB
#kss_ntree CFSG.KD.G2Three.Sec1.R1BPOS CFSG.KD.G2Three.Sec1.Gen2.posB
#kss_ntree CFSG.KD.G2Three.Sec1.R1BSRT CFSG.KD.G2Three.Sec1.Gen2.srtB
#kss_ntree CFSG.KD.G2Three.Sec1.R1BSRI CFSG.KD.G2Three.Sec1.Gen2.sriB
#kss_ntree CFSG.KD.G2Three.Sec1.R1SC CFSG.KD.G2Three.Sec1.Gen2.scC
#kss_ntree CFSG.KD.G2Three.Sec1.R1SD CFSG.KD.G2Three.Sec1.Gen2.scD
#kss_ntree CFSG.KD.G2Three.Sec1.R1SW CFSG.KD.G2Three.Sec1.Gen2.scW
#kss_ntree CFSG.KD.G2Three.Sec1.R1BC CFSG.KD.G2Three.Sec1.Gen2.bcC
#kss_ntree CFSG.KD.G2Three.Sec1.R1BD CFSG.KD.G2Three.Sec1.Gen2.bcD
#kss_ntree CFSG.KD.G2Three.Sec1.R1BW CFSG.KD.G2Three.Sec1.Gen2.bcW
