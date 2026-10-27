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

namespace CFSG.KD.G2Three.Gen

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

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

meta def sqM (a : Nat) : Nat := mulM a a

meta def oneM : Nat := pkM one14
meta def x0M : Nat := pkM x0c
meta def x1M : Nat := pkM x1c
meta def y0M : Nat := pkM y0c
meta def y1M : Nat := pkM y1c
meta def tcM : Nat := mulM (mulM (mulM (mulM (sqM x1M) y1M) x1M) y1M) (sqM x1M)
meta def n0M : Nat := mulM (mulM x0M (sqM y0M)) x0M
meta def n1M : Nat := mulM (mulM x1M (sqM y1M)) x1M
meta def n0iM : Nat := mulM (mulM (sqM x0M) y0M) (sqM x0M)
meta def n1iM : Nat := mulM (mulM (sqM x1M) y1M) (sqM x1M)
meta def wM : Nat := mulM n0M n1M
meta def wiM : Nat := mulM n1iM n0iM
meta def uM : Nat := mulM (mulM wM x0M) wiM
meta def vM : Nat := mulM (mulM wM y0M) wiM
meta def h0M : Nat := mulM (mulM (mulM (mulM (sqM x0M) y0M) x0M) y0M) (sqM x0M)
meta def q2M : Nat := mulM (mulM x1M n1M) (sqM x1M)
meta def nbM : Nat := mulM (mulM uM (sqM vM)) uM
meta def qb2M : Nat := mulM (mulM uM nbM) (sqM uM)

meta def gX : List Nat := [x1M, y1M, uM, vM, h0M]
meta def gS : List Nat := [n1M, q2M, nbM, qb2M, h0M]
meta def gP : List Nat := [x1M, uM]
meta def gA : List Nat := [x0M, x1M, y0M, y1M]
meta def gB : List Nat := gA.map sqM

meta def bfsM (gens : List Nat) (fuel : Nat) :
    Array Nat × Array (Nat × Nat) × Array Nat × Array Nat := Id.run do
  let gs := gens.toArray
  let mut es : Array Nat := #[oneM]
  let mut par : Array (Nat × Nat) := #[]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert oneM 0
  let mut C : Array Nat := #[]
  let mut POS : Array Nat := #[]
  for h in [0:fuel] do
    for s in [0:gs.size] do
      C := C.push es.size
      if h < es.size then
        let y := mulM es[h]! gs[s]!
        match idx.get? y with
        | some p => POS := POS.push p
        | none =>
          POS := POS.push es.size
          idx := idx.insert y es.size
          es := es.push y
          par := par.push (h, s)
      else
        POS := POS.push 0
  C := C.push es.size
  return (es, par, C, POS)

meta def sortM (xs : Array Nat) : List Nat × List Nat :=
  let srt := (Array.range xs.size).qsort (fun a b => xs[a]! < xs[b]!)
  let sri := (Array.range srt.size).foldl (fun acc i => acc.set! srt[i]! i)
    (Array.replicate srt.size 0)
  (srt.toList, sri.toList)

meta def bX := bfsM gX 576
meta def bS := bfsM gS 64
meta def bP := bfsM gP 9

meta def xX : List Nat := bX.1.toList
meta def paX : List Nat := bX.2.1.toList.map (·.1)
meta def pbX : List Nat := bX.2.1.toList.map (·.2)
meta def cX : List Nat := bX.2.2.1.toList
meta def posX : List Nat := bX.2.2.2.toList
meta def srtX : List Nat := (sortM bX.1).1
meta def sriX : List Nat := (sortM bX.1).2

meta def xS : List Nat := bS.1.toList
meta def paS : List Nat := bS.2.1.toList.map (·.1)
meta def pbS : List Nat := bS.2.1.toList.map (·.2)
meta def cS : List Nat := bS.2.2.1.toList
meta def posS : List Nat := bS.2.2.2.toList
meta def srtS : List Nat := (sortM bS.1).1
meta def sriS : List Nat := (sortM bS.1).2

meta def xP : List Nat := bP.1.toList
meta def paP : List Nat := bP.2.1.toList.map (·.1)
meta def pbP : List Nat := bP.2.1.toList.map (·.2)
meta def cP : List Nat := bP.2.2.1.toList
meta def posP : List Nat := bP.2.2.2.toList
meta def srtP : List Nat := (sortM bP.1).1
meta def sriP : List Nat := (sortM bP.1).2

meta def orbM : Array Nat :=
  let A := gA.toArray
  let B := gB.toArray
  parO.foldl (fun acc ps => acc.push (mulM (mulM A[ps.2]! acc[ps.1]!) B[ps.2]!)) #[tcM]

meta def xO : List Nat := orbM.toList
meta def oaO : List Nat := parO.map (·.1)
meta def obO : List Nat := parO.map (·.2)
meta def srtO : List Nat := (sortM orbM).1
meta def sriO : List Nat := (sortM orbM).2

meta def idxM : List Nat :=
  let O := orbM
  let m : Std.HashMap Nat Nat := (List.range O.size).foldl (fun m i => m.insert O[i]! i) {}
  bS.1.toList.map fun a => if mulM a a == oneM && a != oneM then (m.get? a).getD 0 else 0

end CFSG.KD.G2Three.Gen

#kss_ntree CFSG.KD.G2Three.GX CFSG.KD.G2Three.Gen.gX
#kss_ntree CFSG.KD.G2Three.XX CFSG.KD.G2Three.Gen.xX
#kss_ntree CFSG.KD.G2Three.PAX CFSG.KD.G2Three.Gen.paX
#kss_ntree CFSG.KD.G2Three.PBX CFSG.KD.G2Three.Gen.pbX
#kss_ntree CFSG.KD.G2Three.CX CFSG.KD.G2Three.Gen.cX
#kss_ntree CFSG.KD.G2Three.POSX CFSG.KD.G2Three.Gen.posX
#kss_ntree CFSG.KD.G2Three.SRTX CFSG.KD.G2Three.Gen.srtX
#kss_ntree CFSG.KD.G2Three.SRIX CFSG.KD.G2Three.Gen.sriX

#kss_ntree CFSG.KD.G2Three.GS CFSG.KD.G2Three.Gen.gS
#kss_ntree CFSG.KD.G2Three.XS CFSG.KD.G2Three.Gen.xS
#kss_ntree CFSG.KD.G2Three.PAS CFSG.KD.G2Three.Gen.paS
#kss_ntree CFSG.KD.G2Three.PBS CFSG.KD.G2Three.Gen.pbS
#kss_ntree CFSG.KD.G2Three.CS CFSG.KD.G2Three.Gen.cS
#kss_ntree CFSG.KD.G2Three.POSS CFSG.KD.G2Three.Gen.posS
#kss_ntree CFSG.KD.G2Three.SRTS CFSG.KD.G2Three.Gen.srtS
#kss_ntree CFSG.KD.G2Three.SRIS CFSG.KD.G2Three.Gen.sriS

#kss_ntree CFSG.KD.G2Three.GP CFSG.KD.G2Three.Gen.gP
#kss_ntree CFSG.KD.G2Three.XP CFSG.KD.G2Three.Gen.xP
#kss_ntree CFSG.KD.G2Three.PAP CFSG.KD.G2Three.Gen.paP
#kss_ntree CFSG.KD.G2Three.PBP CFSG.KD.G2Three.Gen.pbP
#kss_ntree CFSG.KD.G2Three.CP CFSG.KD.G2Three.Gen.cP
#kss_ntree CFSG.KD.G2Three.POSP CFSG.KD.G2Three.Gen.posP
#kss_ntree CFSG.KD.G2Three.SRTP CFSG.KD.G2Three.Gen.srtP
#kss_ntree CFSG.KD.G2Three.SRIP CFSG.KD.G2Three.Gen.sriP

#kss_ntree CFSG.KD.G2Three.GA CFSG.KD.G2Three.Gen.gA
#kss_ntree CFSG.KD.G2Three.GB CFSG.KD.G2Three.Gen.gB
#kss_ntree CFSG.KD.G2Three.XO CFSG.KD.G2Three.Gen.xO
#kss_ntree CFSG.KD.G2Three.OA CFSG.KD.G2Three.Gen.oaO
#kss_ntree CFSG.KD.G2Three.OB CFSG.KD.G2Three.Gen.obO
#kss_ntree CFSG.KD.G2Three.SRTO CFSG.KD.G2Three.Gen.srtO
#kss_ntree CFSG.KD.G2Three.SRIO CFSG.KD.G2Three.Gen.sriO
#kss_ntree CFSG.KD.G2Three.IDX CFSG.KD.G2Three.Gen.idxM
