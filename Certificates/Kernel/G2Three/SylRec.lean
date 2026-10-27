module

public meta import Lean
meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434G23Check
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public meta import CFSG.Certificates.Kernel.Common.Eval
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

namespace CFSG.KD.G2Three.SylGen

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.RankThree.PartTwo.Sec4.Item434RemG23

meta def bitsM (v : Nat) (l : List Nat) : Nat :=
  l.foldr (fun e acc => 2 * acc + if e == v then 1 else 0) 0

meta def pkM (m : List Nat) : Nat := 2 ^ 196 * bitsM 2 m + bitsM 1 m

meta def LOm : Nat := 2 ^ 196 - 1
meta def RMm : Nat := 2 ^ 14 - 1
meta def CIm : Nat := (List.range 14).foldl (fun a i => a ||| (1 <<< (14 * i))) 0

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

meta def oneM : Nat := pkM one14
meta def gA : Array Nat := #[pkM x0c, pkM x1c, pkM y0c, pkM y1c]

meta def letM (l : Nat) : Nat :=
  if l < 4 then gA[l]! else if l < 8 then mulM gA[l - 4]! gA[l - 4]! else mulM oneM oneM

meta def wordM (w : List Nat) : Nat := w.foldl (fun a l => mulM a (letM l)) oneM

meta def gY : Array Nat := #[gA[0]!, gA[1]!, wordM sylWord]

meta def xYA : Array Nat :=
  sylPar.foldl (fun acc ps => acc.push (mulM acc[ps.1]! gY[ps.2]!)) #[oneM]

meta def idxY : Std.HashMap Nat Nat :=
  (List.range xYA.size).foldl (fun m i => m.insert xYA[i]! i) {}

meta def sortM (xs : Array Nat) : List Nat × List Nat :=
  let srt := (Array.range xs.size).qsort (fun a b => xs[a]! < xs[b]!)
  let sri := (Array.range srt.size).foldl (fun acc i => acc.set! srt[i]! i)
    (Array.replicate srt.size 0)
  (srt.toList, sri.toList)

meta def gYL : List Nat := gY.toList
meta def xY : List Nat := xYA.toList
meta def paY : List Nat := sylPar.map (·.1)
meta def pbY : List Nat := sylPar.map (·.2)
meta def posY : List Nat :=
  (List.range (729 * 3)).map fun i => (idxY.get? (mulM xYA[i / 3]! gY[i % 3]!)).getD 0
meta def srtY : List Nat := (sortM xYA).1
meta def sriY : List Nat := (sortM xYA).2

meta def pwM (E k : Nat) : Nat := if k == 0 then oneM else if k == 1 then E else mulM E E

meta def dPM (E : Nat → Nat) (u : Nat) : Nat :=
  mulM (mulM (mulM (pwM (E 0) (u % 3)) (pwM (E 1) (u / 3 % 3))) (pwM (E 2) (u / 9 % 3)))
    (pwM (E 3) (u / 27 % 3))

meta def dXA : Array Nat :=
  ((List.range 567).map fun k =>
    let D := sylDs.getD (k / 81) []
    dPM (fun a => xYA[D.getD a 0]!) (k % 81)).toArray

meta def dX : List Nat := dXA.toList
meta def dSrt : List Nat :=
  (List.range 7).flatMap fun j => (sortM (dXA.extract (81 * j) (81 * j + 81))).1
meta def dSri : List Nat :=
  (List.range 7).flatMap fun j => (sortM (dXA.extract (81 * j) (81 * j + 81))).2
meta def zW : List Nat :=
  (List.range 7).map fun j =>
    ((List.range 81).find? fun u => dXA[81 * j + u]! == xYA[725]!).getD 0
meta def wY : List Nat :=
  (List.range 729).map fun t =>
    let c := xYA[t]!
    if c == oneM || mulM c (mulM c c) != oneM then 0
    else ((List.range 567).find? fun k => dXA[k]! == c).getD 0

meta def tdA : Array Nat :=
  (conjWords.flatMap fun w => sylZ.map fun z =>
    mulM (mulM (wordM (invWord w)) xYA[z]!) (wordM (invWord (invWord w)))).toArray

meta def tdL : List Nat := tdA.toList

meta def mK : Nat := Id.run do
  let ds := (tdA.toList.foldl (fun (s : Std.HashSet Nat) d => s.insert d) {}).toList
  let mut M := 200
  for _ in [0:100000] do
    let rs := ds.foldl (fun (s : Std.HashSet Nat) d => s.insert (d % M)) {}
    if rs.size == ds.length then return M
    M := M + 1
  return M

meta def mKL : List Nat := [mK]

meta def tkyA : Array Nat := Id.run do
  let mut a := Array.replicate mK 0
  for j in [0:tdA.size] do
    a := a.set! (tdA[j]! % mK) j
  return a

meta def tkyL : List Nat := tkyA.toList

meta def inTM (D : Nat) : Bool := let j := tkyA[D % mK]!; j < 200 && D == tdA[j]!

meta def ppL : List Nat :=
  [(List.range 728).foldl (fun acc k => acc ||| ((paY[k]! + 1024 * pbY[k]!) <<< (12 * k))) 0]

meta def rtpL : List Nat :=
  [(List.range 2187).foldl (fun acc i => acc ||| (posY[i]! <<< (10 * i))) 0]

meta def posA : Array Nat := posY.toArray

meta def nPos : List Nat :=
  (List.range 729).filter fun t =>
    let c := xYA[t]!
    c != oneM && mulM c (mulM c c) == oneM && !inTM c

meta def rowM (a : Nat) : Nat := Id.run do
  let mut r : Array Nat := #[a]
  for k in [0:728] do
    r := r.push posA[3 * r[paY[k]!]! + pbY[k]!]!
  return (List.range 729).foldl (fun acc k => acc ||| (r[k]! <<< (10 * k))) 0

meta def tbL : List Nat :=
  [(List.range 729).foldl (fun acc t => if inTM xYA[t]! then acc ||| (1 <<< t) else acc) 0]

meta def rAll : List Nat := nPos.map rowM

open CFSG.KC.Eval in
meta def rStep : Step := fun args => do
  let rs := match args with
    | #[.nat k] => (rAll.drop (32 * k)).take 32
    | _ => rAll
  return #[(.anonymous, .list (rs.toArray.map fun r => .nat r))]

end CFSG.KD.G2Three.SylGen

#kss_ntree CFSG.KD.G2Three.SylG CFSG.KD.G2Three.SylGen.gYL
#kss_ntree CFSG.KD.G2Three.SylX CFSG.KD.G2Three.SylGen.xY
#kss_ntree CFSG.KD.G2Three.SylPP CFSG.KD.G2Three.SylGen.ppL
#kss_ntree CFSG.KD.G2Three.SylRTP CFSG.KD.G2Three.SylGen.rtpL
#kss_ntree CFSG.KD.G2Three.SylSRT CFSG.KD.G2Three.SylGen.srtY
#kss_ntree CFSG.KD.G2Three.SylSRI CFSG.KD.G2Three.SylGen.sriY

#kss_ntree CFSG.KD.G2Three.SylDX CFSG.KD.G2Three.SylGen.dX
#kss_ntree CFSG.KD.G2Three.SylDSRT CFSG.KD.G2Three.SylGen.dSrt
#kss_ntree CFSG.KD.G2Three.SylDSRI CFSG.KD.G2Three.SylGen.dSri
#kss_ntree CFSG.KD.G2Three.SylZW CFSG.KD.G2Three.SylGen.zW
#kss_ntree CFSG.KD.G2Three.SylW CFSG.KD.G2Three.SylGen.wY

#kss_ntree CFSG.KD.G2Three.SylTD CFSG.KD.G2Three.SylGen.tdL
#kss_ntree CFSG.KD.G2Three.SylTKY CFSG.KD.G2Three.SylGen.tkyL
#kss_ntree CFSG.KD.G2Three.SylMK CFSG.KD.G2Three.SylGen.mKL

#kss_ntree CFSG.KD.G2Three.SylTB CFSG.KD.G2Three.SylGen.tbL
#kc_eval CFSG.KD.G2Three SylR CFSG.KD.G2Three.SylGen.rStep
#kc_eval CFSG.KD.G2Three SylR0 CFSG.KD.G2Three.SylGen.rStep 0
#kc_eval CFSG.KD.G2Three SylR1 CFSG.KD.G2Three.SylGen.rStep 1
#kc_eval CFSG.KD.G2Three SylR2 CFSG.KD.G2Three.SylGen.rStep 2
#kc_eval CFSG.KD.G2Three SylR3 CFSG.KD.G2Three.SylGen.rStep 3
#kc_eval CFSG.KD.G2Three SylR4 CFSG.KD.G2Three.SylGen.rStep 4
#kc_eval CFSG.KD.G2Three SylR5 CFSG.KD.G2Three.SylGen.rStep 5
#kc_eval CFSG.KD.G2Three SylR6 CFSG.KD.G2Three.SylGen.rStep 6
#kc_eval CFSG.KD.G2Three SylR7 CFSG.KD.G2Three.SylGen.rStep 7
