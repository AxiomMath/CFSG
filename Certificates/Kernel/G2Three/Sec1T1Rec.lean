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

namespace CFSG.KD.G2Three.Sec1.Gen1

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

meta def swp (a : Nat) : Nat := (a >>> 392) + ((a &&& LPm) <<< 392)

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

meta def invM (x : Nat) : Nat := Id.run do
  let mut p := x
  for _ in [0:64] do
    let q := mp p x
    if q == oneP then return p
    p := q
  return oneP

meta def cj (g y : Nat) : Nat := mp (mp g y) (invM g)

meta def gH : List Nat := [8, 9, 10]
meta def gK1 : List Nat := [0, 1]
meta def gK2 : List Nat := [2, 3]
meta def gQ1 : List Nat := [5, 1]
meta def gQ2 : List Nat := [6, 3]
meta def gS : List Nat := [5, 1, 6, 3, 4]
meta def gA : List Nat := [5, 1, 6, 3]
meta def gM : List Nat := [20, 23]
meta def gE : List Nat := [13, 15, 11]
meta def gF : List Nat := [12, 13, 11]
meta def gY2 : List Nat := [16, 17, 11]
meta def gY3 : List Nat := [16, 15, 11]

meta def cH := closM mp oneP (gH.map U)
meta def cK1 := closM mp oneP (gK1.map U)
meta def cK2 := closM mp oneP (gK2.map U)
meta def cQ1 := closM mp oneP (gQ1.map U)
meta def cQ2 := closM mp oneP (gQ2.map U)
meta def cS := closM mp oneP (gS.map U)
meta def cA := closM mp oneP (gA.map U)
meta def cM := closM mp oneP (gM.map U)
meta def bE := basisM (gE.map U)
meta def bF := basisM (gF.map U)
meta def bY2 := basisM (gY2.map U)
meta def bY3 := basisM (gY3.map U)
meta def xH := cH.1
meta def xK1 := cK1.1
meta def xK2 := cK2.1
meta def xQ1 := cQ1.1
meta def xQ2 := cQ2.1
meta def xS := cS.1
meta def xA := cA.1
meta def xM := cM.1

meta def dgM (c p : Nat) : Nat := (c / p) % 3
meta def mul22M (a b : Nat) : Nat :=
  ((dgM a 1 * dgM b 1 + dgM a 3 * dgM b 9) % 3) + 3 * ((dgM a 1 * dgM b 3 + dgM a 3 * dgM b 27) % 3) +
    9 * ((dgM a 9 * dgM b 1 + dgM a 27 * dgM b 9) % 3) +
    27 * ((dgM a 9 * dgM b 3 + dgM a 27 * dgM b 27) % 3)

meta def mul3M (p q : Nat) : Nat :=
  ((p >>> (2 * (q &&& 3))) &&& 3) + (((p >>> (2 * ((q >>> 2) &&& 3))) &&& 3) <<< 2) +
    (((p >>> (2 * ((q >>> 4) &&& 3))) &&& 3) <<< 4)
meta def mul33M (x y : Nat) : Nat :=
  mul3M (x &&& 63) (y &&& 63) + (mul3M (x >>> 6) (y >>> 6) <<< 6)

meta def homM (c : Array Nat × Array (Nat × Nat) × Array Nat) (mul : Nat → Nat → Nat) (one : Nat)
    (imgs : List Nat) : Array Nat :=
  c.2.1.foldl (fun acc p => acc.push (mul acc[p.1]! imgs[p.2]!)) #[one]

meta def slU1 : Nat := 75
meta def slB1 : Nat := 15
meta def slOne : Nat := 28
meta def kY := homM cK1 mul22M slOne [slU1, slB1]

meta def pOne : Nat := 2340
meta def pL : List Nat := [585, pOne, 1161, pOne, 1560, pOne, pOne, pOne]
meta def pSig : Nat := 1572
meta def pUA : Array Nat := defs.foldl (fun acc d => acc.push (mul33M acc[d.1]! acc[d.2]!)) pL.toArray
meta def pG : List Nat := gH.map fun i => pUA[i]!
meta def pY := homM cH mul33M pOne pG
meta def cPI := closM mul33M pOne (pG ++ [pSig])

meta def matM (g : Nat) : Nat :=
  (List.range 3).foldl (fun acc j => acc + (find bE (cj g bE[1 <<< j]!) <<< (3 * j))) 0

meta def mG : List Nat := [20, 23, 5, 1, 6, 3, 19]
meta def mL : List Nat := mG.map fun i => matM (U i)

meta def comA : List (Nat × Nat × Nat × Nat) :=
  let g := [5, 1, 6, 3]
  (List.range 4).flatMap fun i => (List.range 4).filterMap fun j =>
    if i < j then
      let x := g[i]!
      let y := g[j]!
      some (if mp (U x) (U y) == mp (U y) (U x) then (x, y, y, x) else (x, y, y, 25 + i))
    else none

meta def rel : List (Nat × Nat × Nat × Nat) :=
  ((List.range defs.length).map fun q => (defs[q]!.1, defs[q]!.2, q + 8, 7)) ++
  [(0, 8, 7, 7), (2, 18, 7, 7), (11, 11, 7, 7), (3, 3, 11, 7), (4, 4, 7, 7),
    (4, 0, 8, 4), (4, 2, 18, 4),
    (0, 2, 2, 0), (0, 3, 3, 0), (1, 2, 2, 1), (1, 3, 3, 1),
    (11, 0, 0, 11), (11, 1, 1, 11), (11, 2, 2, 11), (11, 3, 3, 11), (11, 4, 4, 11),
    (12, 12, 7, 7), (13, 13, 7, 7), (15, 15, 7, 7), (12, 13, 13, 12),
    (13, 15, 15, 13), (16, 16, 7, 7), (17, 17, 7, 7), (16, 17, 17, 16), (16, 15, 15, 16),
    (19, 19, 33, 7), (19, 33, 7, 7),
    (12, 11, 11, 12), (13, 11, 11, 13), (15, 11, 11, 15), (16, 11, 11, 16), (17, 11, 11, 17)] ++
  comA

meta def nrel : List (Nat × Nat × Nat × Nat) :=
  [(0, 7, 7, 7), (2, 7, 7, 7), (11, 7, 7, 7), (19, 7, 7, 7)]

meta def swL : List (Nat × Nat) := [(0, 2), (2, 0), (1, 3), (3, 1), (4, 24), (11, 11), (12, 12),
  (13, 13), (5, 6), (6, 5), (15, 36)]

meta def normL (ga : List Nat) (gb : List Nat) (xs : Array Nat) : List Nat :=
  ga.flatMap fun a => gb.map fun b => find xs (cj (U a) (U b))

meta def nH5 : List Nat := [0, 1, 2, 3, 4]
meta def nK1 := normL nH5 gK1 xK1
meta def nK2 := normL nH5 gK2 xK2
meta def nQ1 := normL nH5 gQ1 xQ1
meta def nQ2 := normL nH5 gQ2 xQ2
meta def nA := normL nH5 gA xA

meta def iH : List Nat := (List.range 8).map fun s => find xH (U s)
meta def iSW : List Nat := gH.map fun i => find xH (swp (U i))

meta def iMU : List Nat := [19, 5, 1, 6, 3]
meta def iM : List Nat := iMU.map fun i => find xM (U i)

meta def gEF : List Nat := [12, 13, 15]
meta def kG : List Nat := [slU1, slB1]

meta def orbRec (T : Array Nat) (a : Nat) (ks : List Nat) (ws : List Nat) :
    List Nat × List Nat × List Nat × List Nat :=
  let rs := ws.map fun w =>
    let k := (ks.find? fun k => cj (U k) (U a) == T[w]! || cj (U k) (U a) == mp T[w]! (U 11)).getD 7
    let y := cj (U k) (U a)
    (k, find T y, if y == T[w]! then 7 else 11)
  (ws, rs.map (·.1), rs.map (·.2.1), rs.map (·.2.2))

meta def zs : List Nat := [oneP, U 11]
meta def outZ (T : Array Nat) : List Nat :=
  (List.range T.size).filter fun w => !(zs.contains T[w]!)
meta def out12 : List Nat :=
  (List.range xA.size).filter fun w => !(mem xQ1 xA[w]!) && !(mem xQ2 xA[w]!)
meta def kX : List Nat := [7, 0, 8, 2, 18, 32, 33, 19, 34]
meta def o1 := orbRec xQ1 5 [7, 0, 8] (outZ xQ1)
meta def o2 := orbRec xQ2 6 [7, 2, 18] (outZ xQ2)
meta def o3 := orbRec xA 12 kX out12

meta def repsM (xs : Array Nat) (K : List Nat) : List Nat := Id.run do
  let mut reps : List Nat := [0]
  for i in [0:xs.size] do
    let x := xs[i]!
    if !(reps.any fun r => K.contains (mp (invM xs[r]!) x)) then
      reps := reps ++ [i]
  return reps

meta def raL : List Nat := repsM xA bE.toList

meta def actRec (tab : Array Nat) (reps : List Nat) (K : Array Nat) (tau : Nat) :
    List Nat × List Nat × List Nat :=
  let W := reps.map fun r => find tab (cj tau tab[r]!)
  let T := W.map fun w =>
    ((List.range reps.length).find? fun p => mem K (mp (invM tab[reps[p]!]!) tab[w]!)).getD 0
  let Z := (W.zip T).map fun (w, p) => find K (mp (invM tab[reps[p]!]!) tab[w]!)
  (W, T, Z)

meta def raA := actRec xA raL bE (U 19)

meta def p4I : List Nat := [0, 0, 0, 1, 1, 2]
meta def p4J : List Nat := [1, 2, 3, 2, 3, 3]

meta def eo : List Nat := [1, 2, 3, 5, 6, 7]
meta def etU : List Nat := eo.flatMap fun u => eo.map fun _ => u
meta def etV : List Nat := eo.flatMap fun _ => eo
meta def etK : List Nat := eo.flatMap fun u => eo.map fun v =>
  ((List.range xM.size).find? fun k => cj xM[k]! bE[u]! == bE[v]!).getD 0
meta def fxK : List Nat := eo.map fun e =>
  ((List.range xM.size).find? fun k => cj xM[k]! bE[e]! != bE[e]!).getD 0

meta def ceL : List Nat := [7, 0, 8]
meta def edI : List Nat := [7, 7, 0]
meta def edJ : List Nat := [0, 8, 8]
meta def edD : List Nat := [8, 0, 8]
meta def edW : List Nat := edD.map fun d =>
  ((List.range 3).find? fun w => !(mem bE (cj (U d) bE[1 <<< w]!))).getD 0

meta def y2W : List Nat := [1, 2, 4].map fun w => find bY2 (cj (U 0) bE[w]!)
meta def y3W : List Nat := [1, 2, 4].map fun w => find bY3 (cj (U 0) bF[w]!)

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
meta def swA := swL.map (·.1)
meta def swB := swL.map (·.2)
meta def xHL := L xH
meta def paH := PA cH
meta def pbH := PB cH
meta def posH := POS cH
meta def srtH := SRT xH
meta def sriH := SRI xH
meta def xK1L := L xK1
meta def paK1 := PA cK1
meta def pbK1 := PB cK1
meta def posK1 := POS cK1
meta def srtK1 := SRT xK1
meta def sriK1 := SRI xK1
meta def xK2L := L xK2
meta def paK2 := PA cK2
meta def pbK2 := PB cK2
meta def posK2 := POS cK2
meta def srtK2 := SRT xK2
meta def sriK2 := SRI xK2
meta def xQ1L := L xQ1
meta def paQ1 := PA cQ1
meta def pbQ1 := PB cQ1
meta def posQ1 := POS cQ1
meta def srtQ1 := SRT xQ1
meta def sriQ1 := SRI xQ1
meta def xQ2L := L xQ2
meta def paQ2 := PA cQ2
meta def pbQ2 := PB cQ2
meta def posQ2 := POS cQ2
meta def srtQ2 := SRT xQ2
meta def sriQ2 := SRI xQ2
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
meta def xML := L xM
meta def paM := PA cM
meta def pbM := PB cM
meta def posM := POS cM
meta def srtM := SRT xM
meta def sriM := SRI xM
meta def xEL := L bE
meta def srtE := SRT bE
meta def sriE := SRI bE
meta def xFL := L bF
meta def srtF := SRT bF
meta def sriF := SRI bF
meta def xY2L := L bY2
meta def srtY2 := SRT bY2
meta def sriY2 := SRI bY2
meta def xY3L := L bY3
meta def srtY3 := SRT bY3
meta def sriY3 := SRI bY3
meta def kYL := L kY
meta def srtKY := SRT kY
meta def sriKY := SRI kY
meta def pYL := L pY
meta def xPIL := L cPI.1
meta def paPI := PA cPI
meta def pbPI := PB cPI
meta def posPI := POS cPI
meta def srtPI := SRT cPI.1
meta def sriPI := SRI cPI.1
meta def pGL := pG ++ [pSig]
meta def pUL := L pUA
meta def o1W := o1.1
meta def o1K := o1.2.1
meta def o1V := o1.2.2.1
meta def o1E := o1.2.2.2
meta def o2W := o2.1
meta def o2K := o2.2.1
meta def o2V := o2.2.2.1
meta def o2E := o2.2.2.2
meta def o3W := o3.1
meta def o3K := o3.2.1
meta def o3V := o3.2.2.1
meta def o3E := o3.2.2.2
meta def raW := raA.1
meta def raT := raA.2.1
meta def raE := raA.2.2

end CFSG.KD.G2Three.Sec1.Gen1

#kss_ntree CFSG.KD.G2Three.Sec1.R1U CFSG.KD.G2Three.Sec1.Gen1.uL
#kss_ntree CFSG.KD.G2Three.Sec1.R1RA CFSG.KD.G2Three.Sec1.Gen1.relA
#kss_ntree CFSG.KD.G2Three.Sec1.R1RB CFSG.KD.G2Three.Sec1.Gen1.relB
#kss_ntree CFSG.KD.G2Three.Sec1.R1RC CFSG.KD.G2Three.Sec1.Gen1.relC
#kss_ntree CFSG.KD.G2Three.Sec1.R1RD CFSG.KD.G2Three.Sec1.Gen1.relD
#kss_ntree CFSG.KD.G2Three.Sec1.R1NA CFSG.KD.G2Three.Sec1.Gen1.nrelA
#kss_ntree CFSG.KD.G2Three.Sec1.R1NB CFSG.KD.G2Three.Sec1.Gen1.nrelB
#kss_ntree CFSG.KD.G2Three.Sec1.R1NC CFSG.KD.G2Three.Sec1.Gen1.nrelC
#kss_ntree CFSG.KD.G2Three.Sec1.R1ND CFSG.KD.G2Three.Sec1.Gen1.nrelD
#kss_ntree CFSG.KD.G2Three.Sec1.R1SWA CFSG.KD.G2Three.Sec1.Gen1.swA
#kss_ntree CFSG.KD.G2Three.Sec1.R1SWB CFSG.KD.G2Three.Sec1.Gen1.swB

#kss_ntree CFSG.KD.G2Three.Sec1.R1HG CFSG.KD.G2Three.Sec1.Gen1.gH
#kss_ntree CFSG.KD.G2Three.Sec1.R1H CFSG.KD.G2Three.Sec1.Gen1.xHL
#kss_ntree CFSG.KD.G2Three.Sec1.R1HPA CFSG.KD.G2Three.Sec1.Gen1.paH
#kss_ntree CFSG.KD.G2Three.Sec1.R1HPB CFSG.KD.G2Three.Sec1.Gen1.pbH
#kss_ntree CFSG.KD.G2Three.Sec1.R1HPOS CFSG.KD.G2Three.Sec1.Gen1.posH
#kss_ntree CFSG.KD.G2Three.Sec1.R1HSRT CFSG.KD.G2Three.Sec1.Gen1.srtH
#kss_ntree CFSG.KD.G2Three.Sec1.R1HSRI CFSG.KD.G2Three.Sec1.Gen1.sriH
#kss_ntree CFSG.KD.G2Three.Sec1.R1IH CFSG.KD.G2Three.Sec1.Gen1.iH
#kss_ntree CFSG.KD.G2Three.Sec1.R1ISW CFSG.KD.G2Three.Sec1.Gen1.iSW

#kss_ntree CFSG.KD.G2Three.Sec1.R1K1G CFSG.KD.G2Three.Sec1.Gen1.gK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1K1 CFSG.KD.G2Three.Sec1.Gen1.xK1L
#kss_ntree CFSG.KD.G2Three.Sec1.R1K1PA CFSG.KD.G2Three.Sec1.Gen1.paK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1K1PB CFSG.KD.G2Three.Sec1.Gen1.pbK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1K1POS CFSG.KD.G2Three.Sec1.Gen1.posK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1K1SRT CFSG.KD.G2Three.Sec1.Gen1.srtK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1K1SRI CFSG.KD.G2Three.Sec1.Gen1.sriK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2G CFSG.KD.G2Three.Sec1.Gen1.gK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2 CFSG.KD.G2Three.Sec1.Gen1.xK2L
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2PA CFSG.KD.G2Three.Sec1.Gen1.paK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2PB CFSG.KD.G2Three.Sec1.Gen1.pbK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2POS CFSG.KD.G2Three.Sec1.Gen1.posK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2SRT CFSG.KD.G2Three.Sec1.Gen1.srtK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1K2SRI CFSG.KD.G2Three.Sec1.Gen1.sriK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1G CFSG.KD.G2Three.Sec1.Gen1.gQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1 CFSG.KD.G2Three.Sec1.Gen1.xQ1L
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1PA CFSG.KD.G2Three.Sec1.Gen1.paQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1PB CFSG.KD.G2Three.Sec1.Gen1.pbQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1POS CFSG.KD.G2Three.Sec1.Gen1.posQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1SRT CFSG.KD.G2Three.Sec1.Gen1.srtQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q1SRI CFSG.KD.G2Three.Sec1.Gen1.sriQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2G CFSG.KD.G2Three.Sec1.Gen1.gQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2 CFSG.KD.G2Three.Sec1.Gen1.xQ2L
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2PA CFSG.KD.G2Three.Sec1.Gen1.paQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2PB CFSG.KD.G2Three.Sec1.Gen1.pbQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2POS CFSG.KD.G2Three.Sec1.Gen1.posQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2SRT CFSG.KD.G2Three.Sec1.Gen1.srtQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Q2SRI CFSG.KD.G2Three.Sec1.Gen1.sriQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1SG CFSG.KD.G2Three.Sec1.Gen1.gS
#kss_ntree CFSG.KD.G2Three.Sec1.R1S CFSG.KD.G2Three.Sec1.Gen1.xSL
#kss_ntree CFSG.KD.G2Three.Sec1.R1SPA CFSG.KD.G2Three.Sec1.Gen1.paS
#kss_ntree CFSG.KD.G2Three.Sec1.R1SPB CFSG.KD.G2Three.Sec1.Gen1.pbS
#kss_ntree CFSG.KD.G2Three.Sec1.R1SPOS CFSG.KD.G2Three.Sec1.Gen1.posS
#kss_ntree CFSG.KD.G2Three.Sec1.R1SSRT CFSG.KD.G2Three.Sec1.Gen1.srtS
#kss_ntree CFSG.KD.G2Three.Sec1.R1SSRI CFSG.KD.G2Three.Sec1.Gen1.sriS
#kss_ntree CFSG.KD.G2Three.Sec1.R1AG CFSG.KD.G2Three.Sec1.Gen1.gA
#kss_ntree CFSG.KD.G2Three.Sec1.R1A CFSG.KD.G2Three.Sec1.Gen1.xAL
#kss_ntree CFSG.KD.G2Three.Sec1.R1APA CFSG.KD.G2Three.Sec1.Gen1.paA
#kss_ntree CFSG.KD.G2Three.Sec1.R1APB CFSG.KD.G2Three.Sec1.Gen1.pbA
#kss_ntree CFSG.KD.G2Three.Sec1.R1APOS CFSG.KD.G2Three.Sec1.Gen1.posA
#kss_ntree CFSG.KD.G2Three.Sec1.R1ASRT CFSG.KD.G2Three.Sec1.Gen1.srtA
#kss_ntree CFSG.KD.G2Three.Sec1.R1ASRI CFSG.KD.G2Three.Sec1.Gen1.sriA
#kss_ntree CFSG.KD.G2Three.Sec1.R1MG CFSG.KD.G2Three.Sec1.Gen1.gM
#kss_ntree CFSG.KD.G2Three.Sec1.R1M CFSG.KD.G2Three.Sec1.Gen1.xML
#kss_ntree CFSG.KD.G2Three.Sec1.R1MPA CFSG.KD.G2Three.Sec1.Gen1.paM
#kss_ntree CFSG.KD.G2Three.Sec1.R1MPB CFSG.KD.G2Three.Sec1.Gen1.pbM
#kss_ntree CFSG.KD.G2Three.Sec1.R1MPOS CFSG.KD.G2Three.Sec1.Gen1.posM
#kss_ntree CFSG.KD.G2Three.Sec1.R1MSRT CFSG.KD.G2Three.Sec1.Gen1.srtM
#kss_ntree CFSG.KD.G2Three.Sec1.R1MSRI CFSG.KD.G2Three.Sec1.Gen1.sriM
#kss_ntree CFSG.KD.G2Three.Sec1.R1IM CFSG.KD.G2Three.Sec1.Gen1.iM
#kss_ntree CFSG.KD.G2Three.Sec1.R1IMU CFSG.KD.G2Three.Sec1.Gen1.iMU
#kss_ntree CFSG.KD.G2Three.Sec1.R1EFG CFSG.KD.G2Three.Sec1.Gen1.gEF
#kss_ntree CFSG.KD.G2Three.Sec1.R1KG CFSG.KD.G2Three.Sec1.Gen1.kG

#kss_ntree CFSG.KD.G2Three.Sec1.R1EG CFSG.KD.G2Three.Sec1.Gen1.gE
#kss_ntree CFSG.KD.G2Three.Sec1.R1E CFSG.KD.G2Three.Sec1.Gen1.xEL
#kss_ntree CFSG.KD.G2Three.Sec1.R1ESRT CFSG.KD.G2Three.Sec1.Gen1.srtE
#kss_ntree CFSG.KD.G2Three.Sec1.R1ESRI CFSG.KD.G2Three.Sec1.Gen1.sriE
#kss_ntree CFSG.KD.G2Three.Sec1.R1FG CFSG.KD.G2Three.Sec1.Gen1.gF
#kss_ntree CFSG.KD.G2Three.Sec1.R1F CFSG.KD.G2Three.Sec1.Gen1.xFL
#kss_ntree CFSG.KD.G2Three.Sec1.R1FSRT CFSG.KD.G2Three.Sec1.Gen1.srtF
#kss_ntree CFSG.KD.G2Three.Sec1.R1FSRI CFSG.KD.G2Three.Sec1.Gen1.sriF
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y2G CFSG.KD.G2Three.Sec1.Gen1.gY2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y2 CFSG.KD.G2Three.Sec1.Gen1.xY2L
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y2SRT CFSG.KD.G2Three.Sec1.Gen1.srtY2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y2SRI CFSG.KD.G2Three.Sec1.Gen1.sriY2
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y3G CFSG.KD.G2Three.Sec1.Gen1.gY3
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y3 CFSG.KD.G2Three.Sec1.Gen1.xY3L
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y3SRT CFSG.KD.G2Three.Sec1.Gen1.srtY3
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y3SRI CFSG.KD.G2Three.Sec1.Gen1.sriY3
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y2W CFSG.KD.G2Three.Sec1.Gen1.y2W
#kss_ntree CFSG.KD.G2Three.Sec1.R1Y3W CFSG.KD.G2Three.Sec1.Gen1.y3W

#kss_ntree CFSG.KD.G2Three.Sec1.R1KY CFSG.KD.G2Three.Sec1.Gen1.kYL
#kss_ntree CFSG.KD.G2Three.Sec1.R1KYSRT CFSG.KD.G2Three.Sec1.Gen1.srtKY
#kss_ntree CFSG.KD.G2Three.Sec1.R1KYSRI CFSG.KD.G2Three.Sec1.Gen1.sriKY
#kss_ntree CFSG.KD.G2Three.Sec1.R1PY CFSG.KD.G2Three.Sec1.Gen1.pYL
#kss_ntree CFSG.KD.G2Three.Sec1.R1PG CFSG.KD.G2Three.Sec1.Gen1.pGL
#kss_ntree CFSG.KD.G2Three.Sec1.R1PU CFSG.KD.G2Three.Sec1.Gen1.pUL
#kss_ntree CFSG.KD.G2Three.Sec1.R1PI CFSG.KD.G2Three.Sec1.Gen1.xPIL
#kss_ntree CFSG.KD.G2Three.Sec1.R1PIPA CFSG.KD.G2Three.Sec1.Gen1.paPI
#kss_ntree CFSG.KD.G2Three.Sec1.R1PIPB CFSG.KD.G2Three.Sec1.Gen1.pbPI
#kss_ntree CFSG.KD.G2Three.Sec1.R1PIPOS CFSG.KD.G2Three.Sec1.Gen1.posPI
#kss_ntree CFSG.KD.G2Three.Sec1.R1PISRT CFSG.KD.G2Three.Sec1.Gen1.srtPI
#kss_ntree CFSG.KD.G2Three.Sec1.R1PISRI CFSG.KD.G2Three.Sec1.Gen1.sriPI

#kss_ntree CFSG.KD.G2Three.Sec1.R1EMG CFSG.KD.G2Three.Sec1.Gen1.mG
#kss_ntree CFSG.KD.G2Three.Sec1.R1EM CFSG.KD.G2Three.Sec1.Gen1.mL

#kss_ntree CFSG.KD.G2Three.Sec1.R1NK1 CFSG.KD.G2Three.Sec1.Gen1.nK1
#kss_ntree CFSG.KD.G2Three.Sec1.R1NK2 CFSG.KD.G2Three.Sec1.Gen1.nK2
#kss_ntree CFSG.KD.G2Three.Sec1.R1NQ1 CFSG.KD.G2Three.Sec1.Gen1.nQ1
#kss_ntree CFSG.KD.G2Three.Sec1.R1NQ2 CFSG.KD.G2Three.Sec1.Gen1.nQ2
#kss_ntree CFSG.KD.G2Three.Sec1.R1NA5 CFSG.KD.G2Three.Sec1.Gen1.nA

#kss_ntree CFSG.KD.G2Three.Sec1.R1O1W CFSG.KD.G2Three.Sec1.Gen1.o1W
#kss_ntree CFSG.KD.G2Three.Sec1.R1O1K CFSG.KD.G2Three.Sec1.Gen1.o1K
#kss_ntree CFSG.KD.G2Three.Sec1.R1O1V CFSG.KD.G2Three.Sec1.Gen1.o1V
#kss_ntree CFSG.KD.G2Three.Sec1.R1O1E CFSG.KD.G2Three.Sec1.Gen1.o1E
#kss_ntree CFSG.KD.G2Three.Sec1.R1O2W CFSG.KD.G2Three.Sec1.Gen1.o2W
#kss_ntree CFSG.KD.G2Three.Sec1.R1O2K CFSG.KD.G2Three.Sec1.Gen1.o2K
#kss_ntree CFSG.KD.G2Three.Sec1.R1O2V CFSG.KD.G2Three.Sec1.Gen1.o2V
#kss_ntree CFSG.KD.G2Three.Sec1.R1O2E CFSG.KD.G2Three.Sec1.Gen1.o2E
#kss_ntree CFSG.KD.G2Three.Sec1.R1O3W CFSG.KD.G2Three.Sec1.Gen1.o3W
#kss_ntree CFSG.KD.G2Three.Sec1.R1O3K CFSG.KD.G2Three.Sec1.Gen1.o3K
#kss_ntree CFSG.KD.G2Three.Sec1.R1O3V CFSG.KD.G2Three.Sec1.Gen1.o3V
#kss_ntree CFSG.KD.G2Three.Sec1.R1O3E CFSG.KD.G2Three.Sec1.Gen1.o3E

#kss_ntree CFSG.KD.G2Three.Sec1.R1RAR CFSG.KD.G2Three.Sec1.Gen1.raL
#kss_ntree CFSG.KD.G2Three.Sec1.R1RAW CFSG.KD.G2Three.Sec1.Gen1.raW
#kss_ntree CFSG.KD.G2Three.Sec1.R1RAT CFSG.KD.G2Three.Sec1.Gen1.raT
#kss_ntree CFSG.KD.G2Three.Sec1.R1RAE CFSG.KD.G2Three.Sec1.Gen1.raE
#kss_ntree CFSG.KD.G2Three.Sec1.R1P4I CFSG.KD.G2Three.Sec1.Gen1.p4I
#kss_ntree CFSG.KD.G2Three.Sec1.R1P4J CFSG.KD.G2Three.Sec1.Gen1.p4J
#kss_ntree CFSG.KD.G2Three.Sec1.R1EO CFSG.KD.G2Three.Sec1.Gen1.eo
#kss_ntree CFSG.KD.G2Three.Sec1.R1ETU CFSG.KD.G2Three.Sec1.Gen1.etU
#kss_ntree CFSG.KD.G2Three.Sec1.R1ETV CFSG.KD.G2Three.Sec1.Gen1.etV
#kss_ntree CFSG.KD.G2Three.Sec1.R1ETK CFSG.KD.G2Three.Sec1.Gen1.etK
#kss_ntree CFSG.KD.G2Three.Sec1.R1FXK CFSG.KD.G2Three.Sec1.Gen1.fxK
#kss_ntree CFSG.KD.G2Three.Sec1.R1CE CFSG.KD.G2Three.Sec1.Gen1.ceL
#kss_ntree CFSG.KD.G2Three.Sec1.R1EDI CFSG.KD.G2Three.Sec1.Gen1.edI
#kss_ntree CFSG.KD.G2Three.Sec1.R1EDJ CFSG.KD.G2Three.Sec1.Gen1.edJ
#kss_ntree CFSG.KD.G2Three.Sec1.R1EDD CFSG.KD.G2Three.Sec1.Gen1.edD
#kss_ntree CFSG.KD.G2Three.Sec1.R1EDW CFSG.KD.G2Three.Sec1.Gen1.edW
