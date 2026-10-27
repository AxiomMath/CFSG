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

namespace CFSG.KD.G2Three.Sec1.Gen

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

meta def letM (l : Nat) : Nat :=
  if l = 0 then gx0 else if l = 1 then gx1 else if l = 2 then gy0 else gy1

meta def wordM (w : List Nat) : Nat := w.foldr (fun l acc => mp (letM l) acc) oneP

meta def k3 : Nat := wordM [0, 2, 0, 0, 3, 2, 2, 3, 3, 2, 2, 3, 0, 2, 2]
meta def tt : Nat := wordM [3, 2, 2, 3, 1, 2, 3, 0, 0, 1, 1, 0, 1, 0, 2, 1, 1]

meta def defs : List (Nat × Nat) :=
  [(0, 2), (1, 3), (1, 1), (0, 1), (11, 2), (8, 4), (6, 5), (2, 6), (0, 3), (16, 4), (0, 0),
    (18, 6), (19, 6), (20, 20), (5, 5), (9, 10), (0, 6), (4, 5), (5, 6), (1, 26), (4, 26),
    (0, 28), (0, 14), (1, 14), (6, 14), (6, 26)]

meta def uA : Array Nat :=
  defs.foldl (fun acc d => acc.push (mp acc[d.1]! acc[d.2]!)) #[a1, b1, a2, b2, h0, k3, tt, oneP]

meta def U (i : Nat) : Nat := uA[i]!

meta def closM (mul : Nat → Nat → Nat) (one : Nat) (gens : List Nat) :
    Array Nat × Array (Nat × Nat) × Array Nat := Id.run do
  let gs := gens.toArray
  let mut es : Array Nat := #[one]
  let mut par : Array (Nat × Nat) := #[]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert one 0
  let mut h := 0
  while h < es.size do
    for s in [0:gs.size] do
      let y := mul es[h]! gs[s]!
      if !idx.contains y then
        idx := idx.insert y es.size
        es := es.push y
        par := par.push (h, s)
    h := h + 1
  let mut pos : Array Nat := #[]
  for e in es do
    for s in [0:gs.size] do
      pos := pos.push ((idx.get? (mul e gs[s]!)).getD 0)
  return (es, par, pos)

meta def sortM (xs : Array Nat) : List Nat × List Nat :=
  let srt := (Array.range xs.size).qsort (fun a b => xs[a]! < xs[b]!)
  let sri := (Array.range srt.size).foldl (fun acc i => acc.set! srt[i]! i)
    (Array.replicate srt.size 0)
  (srt.toList, sri.toList)

meta def find (xs : Array Nat) (x : Nat) : Nat :=
  ((List.range xs.size).find? fun i => xs[i]! == x).getD 0

meta def mem (xs : Array Nat) (x : Nat) : Bool := xs.contains x

meta def basisM (gens : List Nat) : Array Nat :=
  (Array.range (2 ^ gens.length)).map fun c =>
    (List.range gens.length).foldl
      (fun acc i => if c &&& (1 <<< i) != 0 then mp acc gens[i]! else acc) oneP

meta def gB : List Nat := [1, 3, 4, 8]
meta def gP : List Nat := [0, 15]
meta def gC : List Nat := [5, 17]
meta def gJ : List Nat := [1, 13]
meta def gF : List Nat := [8, 9, 10]
meta def gE : List Nat := [9, 12, 10]
meta def gY : List Nat := [9, 10, 4]

meta def cX := closM mp oneP [U 11, U 14]
meta def cS := closM mp oneP ((List.range 5).map U)
meta def cA := closM mp oneP ((List.range 4).map U)
meta def cB := closM mp oneP (gB.map U)
meta def cP := closM mp oneP (gP.map U)
meta def cC := closM mp oneP (gC.map U)
meta def cJ := closM mp oneP (gJ.map U)
meta def bF := basisM (gF.map U)
meta def bE := basisM (gE.map U)
meta def bY := basisM (gY.map U)
meta def xX := cX.1
meta def xS := cS.1
meta def xA := cA.1
meta def xB := cB.1
meta def xP := cP.1
meta def xC := cC.1
meta def xJ := cJ.1

meta def invM (x : Nat) : Nat := Id.run do
  let mut p := x
  for _ in [0:64] do
    let q := mp p x
    if q == oneP then return p
    p := q
  return oneP

meta def cj (g y : Nat) : Nat := mp (mp g y) (invM g)

meta def matM (g : Nat) : Nat :=
  (List.range 3).foldl (fun acc j => acc + (find bF (cj g bF[1 <<< j]!) <<< (3 * j))) 0

meta def mG : List Nat := [11, 14, 0, 15, 5, 17, 1, 2, 3]
meta def mL : List Nat := mG.map fun i => matM (U i)

meta def colM (M v : Nat) : Nat :=
  (List.range 3).foldl
    (fun acc k => if v &&& (1 <<< k) != 0 then acc ^^^ ((M >>> (3 * k)) &&& 7) else acc) 0

meta def mul9M (M N : Nat) : Nat :=
  (List.range 3).foldl (fun acc j => acc ||| (colM M ((N >>> (3 * j)) &&& 7) <<< (3 * j))) 0

meta def c9 := closM mul9M (1 + (2 <<< 3) + (4 <<< 6)) (mL.take 2)

meta def rel : List (Nat × Nat × Nat × Nat) :=
  ((List.range defs.length).map fun q => (defs[q]!.1, defs[q]!.2, q + 8, 7)) ++
  [(21, 20, 7, 7), (22, 5, 7, 7),
    (8, 8, 7, 7), (9, 9, 7, 7), (10, 10, 7, 7), (8, 9, 9, 8), (8, 10, 10, 8), (9, 10, 10, 9),
    (12, 12, 7, 7), (9, 12, 12, 9), (12, 10, 10, 12),
    (4, 4, 7, 7), (9, 4, 4, 9), (10, 4, 4, 10),
    (1, 9, 9, 1), (3, 9, 9, 3), (10, 1, 1, 10), (10, 3, 3, 10),
    (5, 10, 10, 5), (17, 10, 10, 17), (0, 10, 10, 0), (2, 10, 10, 2)]

meta def nrel : List (Nat × Nat × Nat × Nat) :=
  [(20, 7, 7, 7), (5, 7, 7, 7), (20, 9, 9, 20), (20, 10, 10, 20), (20, 23, 23, 20)]

meta def nbL : List Nat := gP.flatMap fun a => gB.map fun b => find xB (cj (U a) (U b))
meta def njL : List Nat := gP.flatMap fun a => gJ.map fun b => find xJ (cj (U a) (U b))

meta def zbL : List Nat := [7, 9, 10, 23]

meta def repsM (xs : Array Nat) (K : List Nat) : List Nat := Id.run do
  let mut reps : List Nat := [0]
  for i in [0:xs.size] do
    let x := xs[i]!
    if !(reps.any fun r => K.contains (mp (invM xs[r]!) x)) then
      reps := reps ++ [i]
  return reps

meta def rjL : List Nat := repsM xJ (zbL.map U)
meta def raL : List Nat := repsM xA bF.toList

meta def actRec (tab : Array Nat) (reps : List Nat) (K : Array Nat) (tau : Nat) :
    List Nat × List Nat × List Nat :=
  let W := reps.map fun r => find tab (cj tau tab[r]!)
  let T := W.map fun w =>
    ((List.range reps.length).find? fun p => mem K (mp (invM tab[reps[p]!]!) tab[w]!)).getD 0
  let Z := (W.zip T).map fun (w, p) => find K (mp (invM tab[reps[p]!]!) tab[w]!)
  (W, T, Z)

meta def rjA := actRec xJ rjL (zbL.map U).toArray (U 20)
meta def raA := actRec xA raL bF (U 5)
meta def rjW := rjA.1
meta def rjT := rjA.2.1
meta def rjZ := rjA.2.2
meta def raW := raA.1
meta def raT := raA.2.1
meta def raF := raA.2.2
meta def p4I : List Nat := [0, 0, 0, 1, 1, 2]
meta def p4J : List Nat := [1, 2, 3, 2, 3, 3]

meta def ywL : List Nat := [1, 2, 4].map fun w => find bY (cj (U 24) bE[w]!)

meta def cbL : List Nat := [7, 5, 25, 14, 30, 31, 32]
meta def czL : List Nat := [7, 6, 24, 26, 27, 28, 33]
meta def ceL : List Nat := [7, 5, 6, 24, 25, 26, 27, 28, 29]

meta def cewL : List Nat := ceL.map fun c => find bE (cj (invM (U c)) (U 10))

meta def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun j => (List.range j).map fun i => (i, j)

meta def dI (cs : List Nat) : List Nat := (pairs cs.length).map fun p => cs[p.1]!
meta def dJ (cs : List Nat) : List Nat := (pairs cs.length).map fun p => cs[p.2]!
meta def dD (cs : List Nat) : List Nat :=
  (pairs cs.length).map fun p => find xX (mp (invM (U cs[p.2]!)) (U cs[p.1]!))

meta def dW (cs : List Nat) (gs : List Nat) (H : Array Nat) : List Nat :=
  (pairs cs.length).map fun p =>
    let d := mp (invM (U cs[p.2]!)) (U cs[p.1]!)
    ((List.range gs.length).find? fun s => !(mem H (cj d gs[s]!))).getD 0

meta def zcL : List Nat := czL.map fun c => find bF (cj (U c) (U 10))
meta def bcL : List Nat := cbL.flatMap fun c => [find bF (cj (U c) (U 9)), find bF (cj (U c) (U 10))]
meta def bcU : List Nat := cbL.flatMap fun c => [c, c]
meta def bcV : List Nat := cbL.flatMap fun _ => [9, 10]
meta def edW : List Nat := dW ceL [bE[1]!, bE[2]!, bE[4]!] bE

meta def iqL : List Nat := xS.toList.map fun x =>
  let q := mp x x
  if mp q q == oneP then find bF q else 0

meta def xs2 : Nat :=
  ((List.range xS.size).find? fun i => !(mem bF (mp xS[i]! xS[i]!))).getD 0

meta def i5 : List Nat := (List.range 7).map fun s => find xX (U s)

meta def L (x : Array Nat) : List Nat := x.toList
meta def PA (c : Array Nat × Array (Nat × Nat) × Array Nat) : List Nat := c.2.1.toList.map (·.1)
meta def PB (c : Array Nat × Array (Nat × Nat) × Array Nat) : List Nat := c.2.1.toList.map (·.2)
meta def POS (c : Array Nat × Array (Nat × Nat) × Array Nat) : List Nat := c.2.2.toList
meta def SRT (x : Array Nat) : List Nat := (sortM x).1
meta def SRI (x : Array Nat) : List Nat := (sortM x).2

meta def uL := L uA
meta def relA := rel.map (·.1)
meta def relB := rel.map (·.2.1)
meta def relC := rel.map (·.2.2.1)
meta def relD := rel.map (·.2.2.2)
meta def nrelA := nrel.map (·.1)
meta def nrelB := nrel.map (·.2.1)
meta def nrelC := nrel.map (·.2.2.1)
meta def nrelD := nrel.map (·.2.2.2)
meta def xXL := L xX
meta def paX := PA cX
meta def pbX := PB cX
meta def posX := POS cX
meta def srtX := SRT xX
meta def sriX := SRI xX
meta def xSL := L xS
meta def paS := PA cS
meta def pbS := PB cS
meta def posS := POS cS
meta def srtS := SRT xS
meta def sriS := SRI xS
meta def xAL := L xA
meta def paA := PA cA
meta def pbA := PB cA
meta def posA := POS cA
meta def srtA := SRT xA
meta def sriA := SRI xA
meta def xBL := L xB
meta def paB := PA cB
meta def pbB := PB cB
meta def posB := POS cB
meta def srtB := SRT xB
meta def sriB := SRI xB
meta def xPL := L xP
meta def paP := PA cP
meta def pbP := PB cP
meta def posP := POS cP
meta def srtP := SRT xP
meta def sriP := SRI xP
meta def xCL := L xC
meta def paC := PA cC
meta def pbC := PB cC
meta def posC := POS cC
meta def srtC := SRT xC
meta def sriC := SRI xC
meta def xJL := L xJ
meta def paJ := PA cJ
meta def pbJ := PB cJ
meta def posJ := POS cJ
meta def srtJ := SRT xJ
meta def sriJ := SRI xJ
meta def xFL := L bF
meta def srtF := SRT bF
meta def sriF := SRI bF
meta def xEL := L bE
meta def srtE := SRT bE
meta def sriE := SRI bE
meta def xYL := L bY
meta def srtY := SRT bY
meta def sriY := SRI bY
meta def x9L := L c9.1
meta def pa9 := PA c9
meta def pb9 := PB c9
meta def pos9 := POS c9
meta def srt9 := SRT c9.1
meta def sri9 := SRI c9.1
meta def p7I := (pairs 7).map (·.1)
meta def p7J := (pairs 7).map (·.2)
meta def edI := dI ceL
meta def edJ := dJ ceL
meta def edD := dD ceL
meta def tpL : List Nat := [find xP (U 20)]
meta def jzL : List Nat := [find xJ (U 9)]
meta def xs2L : List Nat := [xs2]

end CFSG.KD.G2Three.Sec1.Gen

#kss_ntree CFSG.KD.G2Three.Sec1.Q5U CFSG.KD.G2Three.Sec1.Gen.uL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RA CFSG.KD.G2Three.Sec1.Gen.relA
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RB CFSG.KD.G2Three.Sec1.Gen.relB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RC CFSG.KD.G2Three.Sec1.Gen.relC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RD CFSG.KD.G2Three.Sec1.Gen.relD
#kss_ntree CFSG.KD.G2Three.Sec1.Q5NA CFSG.KD.G2Three.Sec1.Gen.nrelA
#kss_ntree CFSG.KD.G2Three.Sec1.Q5NB CFSG.KD.G2Three.Sec1.Gen.nrelB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5NC CFSG.KD.G2Three.Sec1.Gen.nrelC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5ND CFSG.KD.G2Three.Sec1.Gen.nrelD

#kss_ntree CFSG.KD.G2Three.Sec1.Q5X CFSG.KD.G2Three.Sec1.Gen.xXL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5XPA CFSG.KD.G2Three.Sec1.Gen.paX
#kss_ntree CFSG.KD.G2Three.Sec1.Q5XPB CFSG.KD.G2Three.Sec1.Gen.pbX
#kss_ntree CFSG.KD.G2Three.Sec1.Q5XPOS CFSG.KD.G2Three.Sec1.Gen.posX
#kss_ntree CFSG.KD.G2Three.Sec1.Q5XSRT CFSG.KD.G2Three.Sec1.Gen.srtX
#kss_ntree CFSG.KD.G2Three.Sec1.Q5XSRI CFSG.KD.G2Three.Sec1.Gen.sriX
#kss_ntree CFSG.KD.G2Three.Sec1.Q5I5 CFSG.KD.G2Three.Sec1.Gen.i5

#kss_ntree CFSG.KD.G2Three.Sec1.Q5S CFSG.KD.G2Three.Sec1.Gen.xSL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5SPA CFSG.KD.G2Three.Sec1.Gen.paS
#kss_ntree CFSG.KD.G2Three.Sec1.Q5SPB CFSG.KD.G2Three.Sec1.Gen.pbS
#kss_ntree CFSG.KD.G2Three.Sec1.Q5SPOS CFSG.KD.G2Three.Sec1.Gen.posS
#kss_ntree CFSG.KD.G2Three.Sec1.Q5SSRT CFSG.KD.G2Three.Sec1.Gen.srtS
#kss_ntree CFSG.KD.G2Three.Sec1.Q5SSRI CFSG.KD.G2Three.Sec1.Gen.sriS

#kss_ntree CFSG.KD.G2Three.Sec1.Q5A CFSG.KD.G2Three.Sec1.Gen.xAL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5APA CFSG.KD.G2Three.Sec1.Gen.paA
#kss_ntree CFSG.KD.G2Three.Sec1.Q5APB CFSG.KD.G2Three.Sec1.Gen.pbA
#kss_ntree CFSG.KD.G2Three.Sec1.Q5APOS CFSG.KD.G2Three.Sec1.Gen.posA
#kss_ntree CFSG.KD.G2Three.Sec1.Q5ASRT CFSG.KD.G2Three.Sec1.Gen.srtA
#kss_ntree CFSG.KD.G2Three.Sec1.Q5ASRI CFSG.KD.G2Three.Sec1.Gen.sriA

#kss_ntree CFSG.KD.G2Three.Sec1.Q5BG CFSG.KD.G2Three.Sec1.Gen.gB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5B CFSG.KD.G2Three.Sec1.Gen.xBL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5BPA CFSG.KD.G2Three.Sec1.Gen.paB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5BPB CFSG.KD.G2Three.Sec1.Gen.pbB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5BPOS CFSG.KD.G2Three.Sec1.Gen.posB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5BSRT CFSG.KD.G2Three.Sec1.Gen.srtB
#kss_ntree CFSG.KD.G2Three.Sec1.Q5BSRI CFSG.KD.G2Three.Sec1.Gen.sriB

#kss_ntree CFSG.KD.G2Three.Sec1.Q5PG CFSG.KD.G2Three.Sec1.Gen.gP
#kss_ntree CFSG.KD.G2Three.Sec1.Q5P CFSG.KD.G2Three.Sec1.Gen.xPL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5PPA CFSG.KD.G2Three.Sec1.Gen.paP
#kss_ntree CFSG.KD.G2Three.Sec1.Q5PPB CFSG.KD.G2Three.Sec1.Gen.pbP
#kss_ntree CFSG.KD.G2Three.Sec1.Q5PPOS CFSG.KD.G2Three.Sec1.Gen.posP
#kss_ntree CFSG.KD.G2Three.Sec1.Q5PSRT CFSG.KD.G2Three.Sec1.Gen.srtP
#kss_ntree CFSG.KD.G2Three.Sec1.Q5PSRI CFSG.KD.G2Three.Sec1.Gen.sriP

#kss_ntree CFSG.KD.G2Three.Sec1.Q5CG CFSG.KD.G2Three.Sec1.Gen.gC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5C CFSG.KD.G2Three.Sec1.Gen.xCL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CPA CFSG.KD.G2Three.Sec1.Gen.paC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CPB CFSG.KD.G2Three.Sec1.Gen.pbC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CPOS CFSG.KD.G2Three.Sec1.Gen.posC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CSRT CFSG.KD.G2Three.Sec1.Gen.srtC
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CSRI CFSG.KD.G2Three.Sec1.Gen.sriC

#kss_ntree CFSG.KD.G2Three.Sec1.Q5JG CFSG.KD.G2Three.Sec1.Gen.gJ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5J CFSG.KD.G2Three.Sec1.Gen.xJL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5JPA CFSG.KD.G2Three.Sec1.Gen.paJ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5JPB CFSG.KD.G2Three.Sec1.Gen.pbJ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5JPOS CFSG.KD.G2Three.Sec1.Gen.posJ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5JSRT CFSG.KD.G2Three.Sec1.Gen.srtJ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5JSRI CFSG.KD.G2Three.Sec1.Gen.sriJ

#kss_ntree CFSG.KD.G2Three.Sec1.Q5FG CFSG.KD.G2Three.Sec1.Gen.gF
#kss_ntree CFSG.KD.G2Three.Sec1.Q5F CFSG.KD.G2Three.Sec1.Gen.xFL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5FSRT CFSG.KD.G2Three.Sec1.Gen.srtF
#kss_ntree CFSG.KD.G2Three.Sec1.Q5FSRI CFSG.KD.G2Three.Sec1.Gen.sriF
#kss_ntree CFSG.KD.G2Three.Sec1.Q5EG CFSG.KD.G2Three.Sec1.Gen.gE
#kss_ntree CFSG.KD.G2Three.Sec1.Q5E CFSG.KD.G2Three.Sec1.Gen.xEL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5ESRT CFSG.KD.G2Three.Sec1.Gen.srtE
#kss_ntree CFSG.KD.G2Three.Sec1.Q5ESRI CFSG.KD.G2Three.Sec1.Gen.sriE
#kss_ntree CFSG.KD.G2Three.Sec1.Q5YG CFSG.KD.G2Three.Sec1.Gen.gY
#kss_ntree CFSG.KD.G2Three.Sec1.Q5Y CFSG.KD.G2Three.Sec1.Gen.xYL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5YSRT CFSG.KD.G2Three.Sec1.Gen.srtY
#kss_ntree CFSG.KD.G2Three.Sec1.Q5YSRI CFSG.KD.G2Three.Sec1.Gen.sriY

#kss_ntree CFSG.KD.G2Three.Sec1.Q5MG CFSG.KD.G2Three.Sec1.Gen.mG
#kss_ntree CFSG.KD.G2Three.Sec1.Q5M CFSG.KD.G2Three.Sec1.Gen.mL
#kss_ntree CFSG.KD.G2Three.Sec1.Q59 CFSG.KD.G2Three.Sec1.Gen.x9L
#kss_ntree CFSG.KD.G2Three.Sec1.Q59PA CFSG.KD.G2Three.Sec1.Gen.pa9
#kss_ntree CFSG.KD.G2Three.Sec1.Q59PB CFSG.KD.G2Three.Sec1.Gen.pb9
#kss_ntree CFSG.KD.G2Three.Sec1.Q59POS CFSG.KD.G2Three.Sec1.Gen.pos9
#kss_ntree CFSG.KD.G2Three.Sec1.Q59SRT CFSG.KD.G2Three.Sec1.Gen.srt9
#kss_ntree CFSG.KD.G2Three.Sec1.Q59SRI CFSG.KD.G2Three.Sec1.Gen.sri9

#kss_ntree CFSG.KD.G2Three.Sec1.Q5NBW CFSG.KD.G2Three.Sec1.Gen.nbL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5NJW CFSG.KD.G2Three.Sec1.Gen.njL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5ZB CFSG.KD.G2Three.Sec1.Gen.zbL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RJ CFSG.KD.G2Three.Sec1.Gen.rjL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RJW CFSG.KD.G2Three.Sec1.Gen.rjW
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RJT CFSG.KD.G2Three.Sec1.Gen.rjT
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RJZ CFSG.KD.G2Three.Sec1.Gen.rjZ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RAR CFSG.KD.G2Three.Sec1.Gen.raL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RAW CFSG.KD.G2Three.Sec1.Gen.raW
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RAT CFSG.KD.G2Three.Sec1.Gen.raT
#kss_ntree CFSG.KD.G2Three.Sec1.Q5RAF CFSG.KD.G2Three.Sec1.Gen.raF
#kss_ntree CFSG.KD.G2Three.Sec1.Q5P4I CFSG.KD.G2Three.Sec1.Gen.p4I
#kss_ntree CFSG.KD.G2Three.Sec1.Q5P4J CFSG.KD.G2Three.Sec1.Gen.p4J
#kss_ntree CFSG.KD.G2Three.Sec1.Q5YW CFSG.KD.G2Three.Sec1.Gen.ywL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CEW CFSG.KD.G2Three.Sec1.Gen.cewL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CE CFSG.KD.G2Three.Sec1.Gen.ceL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5P7I CFSG.KD.G2Three.Sec1.Gen.p7I
#kss_ntree CFSG.KD.G2Three.Sec1.Q5P7J CFSG.KD.G2Three.Sec1.Gen.p7J
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CZ CFSG.KD.G2Three.Sec1.Gen.czL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CZW CFSG.KD.G2Three.Sec1.Gen.zcL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CBU CFSG.KD.G2Three.Sec1.Gen.bcU
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CBV CFSG.KD.G2Three.Sec1.Gen.bcV
#kss_ntree CFSG.KD.G2Three.Sec1.Q5CBW CFSG.KD.G2Three.Sec1.Gen.bcL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5EDI CFSG.KD.G2Three.Sec1.Gen.edI
#kss_ntree CFSG.KD.G2Three.Sec1.Q5EDJ CFSG.KD.G2Three.Sec1.Gen.edJ
#kss_ntree CFSG.KD.G2Three.Sec1.Q5EDD CFSG.KD.G2Three.Sec1.Gen.edD
#kss_ntree CFSG.KD.G2Three.Sec1.Q5EDW CFSG.KD.G2Three.Sec1.Gen.edW
#kss_ntree CFSG.KD.G2Three.Sec1.Q5IQ CFSG.KD.G2Three.Sec1.Gen.iqL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5TP CFSG.KD.G2Three.Sec1.Gen.tpL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5JZ CFSG.KD.G2Three.Sec1.Gen.jzL
#kss_ntree CFSG.KD.G2Three.Sec1.Q5XS2 CFSG.KD.G2Three.Sec1.Gen.xs2L
