module

public meta import Certificates.Data.RudvalisFF81Sp6ShortRoot
public meta import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoData
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

namespace CFSG.KC.Misc.Sp6SRGen

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

meta def pkM (m : List Nat) : Nat := m.foldr (fun e acc => e + 2 * acc) 0

meta def oneM : Nat := 34630287489

meta def jM : Nat := 4328915976

meta def rowM (a i : Nat) : Nat := (a >>> (6 * i)) &&& 63

meta def mulM (a b : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:6] do
    let ri := rowM a i
    let mut acc := 0
    for k in [0:6] do
      if (ri >>> k) &&& 1 == 1 then acc := acc ^^^ rowM b k
    r := r ||| (acc <<< (6 * i))
  return r

meta def trM (a : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:6] do
    for j in [0:6] do
      if (a >>> (6 * i + j)) &&& 1 == 1 then r := r ||| (1 <<< (6 * j + i))
  return r

meta def invM (a : Nat) : Nat := mulM (mulM jM (trM a)) jM

meta def conjM (g x : Nat) : Nat := mulM (mulM g x) (invM g)

meta def commM (x y : Nat) : Bool := mulM x y == mulM y x

meta def bfs (gens : Array Nat) (start : Nat) (st : Nat → Nat → Nat) :
    Array Nat × Array (Nat × Nat) := Id.run do
  let mut E : Array Nat := #[start]
  let mut P : Array (Nat × Nat) := #[(0, 0)]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert start 0
  let mut k := 0
  while k < E.size do
    for l in [0:gens.size] do
      let h := st E[k]! gens[l]!
      if !idx.contains h then
        idx := idx.insert h E.size
        E := E.push h
        P := P.push (k, l)
    k := k + 1
  return (E, P)

meta def posMap (E : Array Nat) : Std.HashMap Nat Nat :=
  (List.range E.size).foldl (fun m t => m.insert E[t]! t) {}

meta def sortOrd (E : Array Nat) : List Nat :=
  ((Array.range E.size).qsort fun a b => E[a]! < E[b]!).toList

meta def packP (P : Array (Nat × Nat)) : List Nat := (P.map fun (p, l) => p + 2 ^ 24 * l).toList

meta def closTab (E gens : Array Nat) : List Nat :=
  let m := posMap E
  (List.range E.size).flatMap fun k => (List.range gens.size).map fun l =>
    m.getD (mulM E[k]! gens[l]!) 0

meta def pathTo (P : Array (Nat × Nat)) (k0 : Nat) : List Nat := Id.run do
  let mut k := k0
  let mut w : List Nat := []
  while k != 0 do
    let (p, l) := P[k]!
    w := l :: w
    k := p
  return w

meta def packW (b : Nat) (w : List Nat) : Nat :=
  w.length + 16 * (w.zipIdx.foldl (fun acc (l, i) => acc + l * b ^ i) 0)

meta def s0 : Nat := pkM srC
meta def zz : Array Nat := #[pkM zCode0, pkM zCode1, pkM zCode2]
meta def uu : Nat := mulM zz[1]! zz[2]!
meta def ww : Nat := mulM zz[1]! (mulM zz[2]! zz[2]!)
meta def x2 : Nat := mulM zz[0]! uu
meta def x3 : Nat := mulM (mulM zz[0]! zz[0]!) uu
meta def cg : Array Nat := (cP.map fun cc => pkM cc.1).toArray
meta def cgi : Array Nat := (cP.map fun cc => pkM cc.2).toArray

meta def kyL : List Nat :=
  [s0, zz[0]!, zz[1]!, zz[2]!, uu, ww, x2, x3, mulM ww ww, pkM aC, pkM bC, pkM aI, pkM bI,
    cg[0]!, cg[1]!, cgi[0]!, cgi[1]!]

meta def tG : Array Nat := #[59282212195, 30852665269, 34823917731, 11168021015]

meta def tgL : List Nat := tG.toList

meta def cB : Array Nat × Array (Nat × Nat) := bfs #[cg[0]!, cg[1]!, cgi[0]!, cgi[1]!] oneM mulM

meta def twL : List Nat :=
  let m := posMap cB.1
  tgL.map fun g => packW 8 (pathTo cB.2 (m.getD g 0))

meta def tB : Array Nat × Array (Nat × Nat) := bfs tG oneM mulM
meta def tE : Array Nat := tB.1
meta def teL : List Nat := tE.toList
meta def tpL : List Nat := packP tB.2
meta def tsL : List Nat := sortOrd tE
meta def tcL : List Nat := closTab tE tG

meta def zB : Array Nat × Array (Nat × Nat) := bfs #[zz[0]!, uu] oneM mulM
meta def ezL : List Nat := zB.1.toList
meta def pzL : List Nat := packP zB.2
meta def szL : List Nat := sortOrd zB.1
meta def czL : List Nat := closTab zB.1 #[zz[0]!, uu]

meta def cc : Nat := mulM zz[0]! uu
meta def ciL : List Nat := let m := posMap zB.1; [m.getD cc 0, m.getD (invM cc) 0]

meta def r3Set : Array Nat :=
  let m := posMap tE
  let ci := invM cc
  tE.filter fun x => m.contains (mulM (mulM ci x) cc)

meta def closSize (gens : Array Nat) : Nat := (bfs gens oneM mulM).1.size

meta def tagOf (n : Nat) : Nat := if n == 8 then 0 else if n == 32 then 1 else 2

meta def orbits : Array (Nat × Array Nat × Array (Nat × Nat) × Nat) := Id.run do
  let tm := posMap tE
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array (Nat × Array Nat × Array (Nat × Nat) × Nat) := #[]
  for x in tE do
    if x == oneM || x == s0 || !r3Set.contains x || seen.contains x then continue
    let o := bfs #[cg[0]!, cg[1]!] x (fun y g => conjM g y)
    for y in o.1 do seen := seen.insert y
    out := out.push (tm.getD x 0, o.1, o.2, tagOf (closSize (o.1.push s0)))
  return out.qsort fun a b => a.2.2.2 < b.2.2.2 || (a.2.2.2 == b.2.2.2 && a.1 < b.1)

meta def ofArr : Array Nat := Id.run do
  let mut r : Array Nat := #[0]
  for o in orbits do r := r.push (r.back! + o.2.1.size)
  return r

meta def oeL : List Nat := orbits.toList.flatMap fun o => o.2.1.toList
meta def opL : List Nat := orbits.toList.flatMap fun o => packP o.2.2.1
meta def ofL : List Nat := ofArr.toList
meta def riL : List Nat := orbits.toList.map fun o => o.1
meta def otL : List Nat := orbits.toList.map fun o => o.2.2.2

meta def prim (t : Nat) : Nat := (orbits.toList.findIdx? fun o => o.2.2.2 == t).getD 0

meta def oeA : Array Nat := oeL.toArray

meta def ocM (k : Nat) : Nat := if k == 126 then s0 else oeA[k]!

meta def gensOf (t : Nat) : Array Nat := Id.run do
  let j := prim t
  let n := if t == 0 then 8 else if t == 1 then 32 else 128
  let mut g : Array Nat := #[126]
  for k in [ofArr[j]!:ofArr[j+1]!] do
    if closSize (g.map ocM) == n then break
    let cur := (bfs (g.map ocM) oneM mulM).1
    if !cur.contains oeA[k]! then g := g.push k
  return g

meta def rTabs : Array (Array Nat × Array (Nat × Nat)) :=
  #[0, 1, 2].map fun t => bfs ((gensOf t).map ocM) oneM mulM

meta def reL : List Nat := rTabs.toList.flatMap fun b => b.1.toList
meta def rpL : List Nat := rTabs.toList.flatMap fun b => packP b.2
meta def rsL : List Nat := rTabs.toList.flatMap fun b => sortOrd b.1
meta def rcL : List Nat :=
  (List.range 3).flatMap fun t => closTab rTabs[t]!.1 ((gensOf t).map ocM)
meta def rgL : List Nat := (List.range 3).flatMap fun t => (gensOf t).toList
meta def ngL : List Nat := (List.range 3).map fun t => (gensOf t).size

meta def roL : List Nat :=
  [0, rTabs[0]!.1.size, rTabs[0]!.1.size + rTabs[1]!.1.size,
    rTabs[0]!.1.size + rTabs[1]!.1.size + rTabs[2]!.1.size]
meta def goL : List Nat := [0, ngL[0]!, ngL[0]! + ngL[1]!]
meta def coL : List Nat :=
  [0, rTabs[0]!.1.size * ngL[0]!, rTabs[0]!.1.size * ngL[0]! + rTabs[1]!.1.size * ngL[1]!]

meta def miL : List Nat := orbits.toList.flatMap fun o =>
  let m := posMap rTabs[o.2.2.2]!.1
  o.2.1.toList.map fun y => m.getD y 0

meta def swOf (j : Nat) : Nat :=
  let t := otL[j]!
  let letters := (List.range' ofArr[j]! (ofArr[j+1]! - ofArr[j]!)).toArray.push 126
  let b := bfs (letters.map ocM) oneM mulM
  let target := oeA[ofArr[prim t]!]!
  let k := (posMap b.1).getD target 0
  packW 128 ((pathTo b.2 k).map fun l => letters[l]!)

meta def ppL : List Nat := [prim 0, prim 1, prim 2]

meta def swL : List Nat :=
  (List.range orbits.size).map fun j => if j == prim otL[j]! then 0 else swOf j

meta def cvL : List Nat :=
  let m := posMap oeA
  rTabs[2]!.1.toList.map fun y => m.getD y 0

meta def mxL : List Nat := Id.run do
  let m := posMap oeA
  let r1 := rTabs[0]!.1
  let r2 := rTabs[1]!.1
  for a in [0:r1.size] do
    for b in [0:r2.size] do
      let k := m.getD (mulM r1[a]! r2[b]!) 1000
      if k < 1000 then
        let j := (List.range orbits.size).find? fun j => ofArr[j]! ≤ k && k < ofArr[j+1]!
        if otL[j.getD 0]! == 2 then return [a, b, k, j.getD 0]
  return [0, 0, 0, 0]

meta def nbL : List Nat :=
  let srt := (sortOrd tE).toArray
  let qm := posMap rTabs[2]!.1
  let ci := invM cc
  (List.range 512).map fun k =>
    let x := tE[k]!
    match qm.get? x with
    | some j => 1048576 + j
    | none =>
      let y := mulM (mulM ci x) cc
      ((List.range 512).find? fun i => y < tE[srt[i]!]!).getD 512

meta def hA : Array Nat := #[pkM aC, pkM bC]
meta def oB : Array Nat × Array (Nat × Nat) := bfs hA s0 (fun x g => conjM g x)
meta def oeS : List Nat := oB.1.toList
meta def opS : List Nat := packP oB.2
meta def osS : List Nat := sortOrd oB.1

meta def recOf (x : Nat) : Nat := Id.run do
  for t in [0:512] do
    for j in [0:9] do
      if mulM tE[t]! zB.1[j]! == x then return t + 512 * j
  return 0

meta def kG : Array Nat := #[17247250697, 51808389513]
meta def kB : Array Nat × Array (Nat × Nat) := bfs kG oneM mulM
meta def kE : Array Nat := kB.1
meta def keL : List Nat := kE.toList
meta def kpL : List Nat := packP kB.2
meta def ksL : List Nat := sortOrd kE
meta def kcL : List Nat := closTab kE kG
meta def kiL : List Nat := let m := posMap kE; keL.map fun x => m.getD (invM x) 0
meta def kgL : List Nat := kG.toList.map recOf

meta def zcB : Array Nat × Array (Nat × Nat) := bfs #[cg[0]!, cg[1]!] zz[0]! (fun y g => conjM g y)
meta def zeL : List Nat := zcB.1.toList
meta def zpL : List Nat := packP zcB.2
meta def zsL : List Nat := sortOrd zcB.1

meta def yG : Array Nat := #[42927373399, 50463194667]
meta def yB : Array Nat × Array (Nat × Nat) := bfs yG oneM mulM
meta def yeL : List Nat := yB.1.toList
meta def ypL : List Nat := packP yB.2
meta def ysL : List Nat := sortOrd yB.1
meta def ycL : List Nat := closTab yB.1 yG
meta def ygL : List Nat := yG.toList.map recOf

meta def xcB : Array Nat × Array (Nat × Nat) := bfs #[cg[0]!, cg[1]!] x2 (fun y g => conjM g y)
meta def xeL : List Nat := xcB.1.toList
meta def xpL : List Nat := packP xcB.2
meta def xsL : List Nat := sortOrd xcB.1

meta def pow4M (v : Nat) : Nat := mulM (mulM v v) (mulM v v)

meta def wiL : List Nat :=
  let y := yB.1
  let i1 := ((List.range y.size).find? fun i =>
    pow4M y[i]! == oneM && y[i]! != oneM && y[i]! != s0).getD 0
  let i2 := ((List.range kE.size).find? fun i =>
    let v := kE[i]!
    mulM v v == oneM && v != oneM && v != s0 &&
      kE.all fun g => commM (conjM g v) v).getD 0
  [i1, i2]

meta def r2Gens : Array Nat := (gensOf 1).map ocM

meta def kwL : List Nat := keL.map fun v =>
  if mulM v v != oneM || r2Gens.all (commM v) then 0 else
  ((List.range kE.size).find? fun k => !commM (conjM kE[k]! v) v).getD 0

meta def r3T : Array Nat := rTabs[2]!.1
meta def idxC (x : Nat) : List Nat := (List.range 128).filter fun i => commM r3T[i]! x
meta def izL : List Nat := idxC zz[0]!
meta def i2L : List Nat := idxC x2
meta def i3L : List Nat := idxC x3

meta def xGens : Array Nat := ((i2L ++ i3L).map fun i => r3T[i]!).toArray
meta def xB : Array Nat × Array (Nat × Nat) := bfs xGens oneM mulM
meta def xA : Array Nat := xB.1
meta def xaL : List Nat := xA.toList
meta def xpA : List Nat := packP xB.2
meta def xsA : List Nat := sortOrd xA
meta def xcA : List Nat := closTab xA xGens
meta def xzL : List Nat := xaL.map fun q =>
  if q == oneM || q == s0 then 0 else ((List.range xA.size).find? fun w => !commM xA[w]! q).getD 0

meta def agL : List Nat := Id.run do
  let m := posMap xA
  let si := m.getD s0 0
  for a in [0:xA.size] do
    for b in [a+1:xA.size] do
      let g := #[s0, xA[a]!, xA[b]!]
      let e := (bfs g oneM mulM).1
      if e.size == 8 && e.all (fun x => mulM x x == oneM && e.all (commM x)) then
        return [si, a, b]
  return [0, 0, 0]

meta def aGens : Array Nat := (agL.map fun i => xA[i]!).toArray
meta def aB : Array Nat × Array (Nat × Nat) := bfs aGens oneM mulM
meta def aeL : List Nat := aB.1.toList
meta def apL : List Nat := packP aB.2
meta def asL : List Nat := sortOrd aB.1
meta def acL : List Nat := closTab aB.1 aGens
meta def aiL : List Nat := [(posMap aB.1).getD s0 0]

end CFSG.KC.Misc.Sp6SRGen

end
