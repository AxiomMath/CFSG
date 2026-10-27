module

public meta import Certificates.Data.RudvalisFF81Sp6Transv
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

namespace CFSG.KC.Misc.Sp6TransvGen

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
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

meta def powM (a n : Nat) : Nat := Id.run do
  let mut r := oneM
  for _ in [0:n] do r := mulM r a
  return r

meta def s0 : Nat := pkM CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv.s0C
meta def zz : Array Nat := #[pkM zCode0, pkM zCode1, pkM zCode2]
meta def tt : Nat := pkM tCode
meta def csg : Array Nat := #[pkM csG0, pkM csG1]
meta def qg : Array Nat := #[pkM qG0, pkM qG1, pkM qG2, pkM qG3, pkM qG4]
meta def hA : Array Nat := #[pkM aC, pkM bC]

meta def tG : Array Nat := #[1972799986, 21178728242, 1658752032, 54712953811]

meta def gT : Nat := 68140371189

meta def ksL : List Nat :=
  [s0, zz[0]!, zz[1]!, zz[2]!, tt, csg[0]!, csg[1]!, pkM csG0I, pkM csG1I, hA[0]!, hA[1]!,
    pkM aI, pkM bI]

meta def tgL : List Nat := tG.toList
meta def qgL : List Nat := qg.toList

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

meta def tB : Array Nat × Array (Nat × Nat) := bfs tG oneM mulM
meta def tE : Array Nat := tB.1
meta def eL : List Nat := tE.toList
meta def pL : List Nat := packP tB.2
meta def sL : List Nat := sortOrd tE
meta def cL : List Nat := closTab tE tG

meta def qE : Array Nat := Id.run do
  let mut E : Array Nat := #[]
  for m in [0:32] do
    let mut x := oneM
    for l in [0:5] do
      if (m >>> l) &&& 1 == 1 then x := mulM x qg[l]!
    E := E.push x
  return E

meta def topBit (m : Nat) : Nat := (List.range 5).foldl (fun b l => if (m >>> l) &&& 1 == 1 then l else b) 0

meta def qeL : List Nat := qE.toList
meta def qpL : List Nat :=
  (List.range 32).map fun m => if m == 0 then 0 else (m - 2 ^ topBit m) + 2 ^ 24 * topBit m
meta def qsL : List Nat := sortOrd qE
meta def qcL : List Nat := closTab qE qg

meta def cc : Nat := mulM csg[0]! csg[0]!

meta def nbL : List Nat :=
  let srt := (sortOrd tE).toArray
  let qm := posMap qE
  let ci := invM cc
  (List.range 512).map fun k =>
    let x := tE[k]!
    match qm.get? x with
    | some j => 1048576 + j
    | none =>
      let y := mulM (mulM ci x) cc
      ((List.range 512).find? fun i => y < tE[srt[i]!]!).getD 512

meta def kB : Array Nat × Array (Nat × Nat) := bfs csg oneM mulM
meta def kE : Array Nat := kB.1.extract 0 12
meta def kL : List Nat := kE.toList
meta def kpL : List Nat := packP (kB.2.extract 0 12)
meta def kiL : List Nat := kL.map invM

meta def spans : List Nat × List Nat := Id.run do
  let qm := posMap qE
  let mut sq : List Nat := []
  let mut sk : List Nat := []
  for m in [0:32] do
    let q := qE[m]!
    if q == oneM || q == s0 then continue
    let mut span : List Nat := [0]
    let mut pick : List Nat := []
    for k in [1:12] do
      if pick.length < 5 then
        let j := qm.getD (conjM kE[k]! q) 0
        if !span.contains j then
          pick := pick ++ [k]
          span := span ++ span.map (· ^^^ j)
    sq := sq ++ [m]
    sk := sk ++ pick
  return (sq, sk)

meta def sqL : List Nat := spans.1
meta def skL : List Nat := spans.2

meta def spanB : List (Array Nat × Array (Nat × Nat)) :=
  (List.range 30).map fun m =>
    let q := qE[sqL[m]!]!
    let gens := (List.range 5).toArray.map fun l => conjM kE[skL[5 * m + l]!]! q
    bfs gens oneM mulM

meta def seL : List Nat := spanB.flatMap fun b => b.1.toList
meta def sppL : List Nat := spanB.flatMap fun b => packP b.2
meta def ssL : List Nat := spanB.flatMap fun b => sortOrd b.1

meta def zB : Array Nat × Array (Nat × Nat) := bfs #[zz[0]!, zz[2]!] oneM mulM
meta def ezL : List Nat := zB.1.toList
meta def pzL : List Nat := packP zB.2
meta def szL : List Nat := sortOrd zB.1
meta def czL : List Nat := closTab zB.1 #[zz[0]!, zz[2]!]

meta def twL : List Nat :=
  let m := posMap kB.1
  tG.toList.map fun g => Id.run do
    let mut k := m.getD g 0
    let mut w : List Nat := []
    while k != 0 do
      let (p, l) := kB.2[k]!
      w := l :: w
      k := p
    return w.length + 16 * (w.zipIdx.foldl (fun acc (l, i) => acc + l * 8 ^ i) 0)

meta def oB : Array Nat × Array (Nat × Nat) := bfs hA s0 (fun x g => conjM g x)
meta def oeL : List Nat := oB.1.toList
meta def opL : List Nat := packP oB.2
meta def osL : List Nat := sortOrd oB.1

meta def letters : Array Nat :=
  #[pkM fl0C, s0, pkM fl2C, tt, zz[0]!, zz[1]!, zz[2]!, gT]

meta def lcL : List Nat := letters.toList
meta def liL : List Nat := letters.toList.map invM
meta def reps : Array Nat := #[zz[1]!, mulM zz[0]! zz[1]!, mulM (mulM zz[0]! zz[1]!) zz[2]!]
meta def repL : List Nat := reps.toList

meta def reach : Std.HashMap Nat (Nat × List Nat) := Id.run do
  let mut out : Std.HashMap Nat (Nat × List Nat) := {}
  for ri in [0:3] do
    let mut seen : Std.HashMap Nat (List Nat) := ({} : Std.HashMap Nat (List Nat)).insert reps[ri]! []
    let mut frontier : Array (Nat × List Nat) := #[(reps[ri]!, [])]
    for _ in [0:6] do
      let mut nxt : Array (Nat × List Nat) := #[]
      for (x, w) in frontier do
        for li in [0:8] do
          let y := conjM letters[li]! x
          if !seen.contains y then
            seen := seen.insert y (li :: w)
            nxt := nxt.push (y, li :: w)
      frontier := nxt
    for (x, w) in seen.toList do
      if !out.contains x then out := out.insert x (ri, w)
  return out

meta def wrL : List Nat :=
  (List.range 81).map fun w =>
    let a := w / 27
    let b := (w / 9) % 3
    let c := (w / 3) % 3
    let j := w % 3
    let x := mulM (mulM (mulM (powM zz[0]! a) (powM zz[1]! b)) (powM zz[2]! c)) (powM tt j)
    if mulM (mulM x x) x != oneM || x == oneM then 0 else
    match reach.get? x with
    | none => 0
    | some (ri, g) =>
      let v := (g.zipIdx.foldl fun acc (l, i) => acc + l * 8 ^ i) 0
      1 + ri + 4 * (g.length + 16 * v)

end CFSG.KC.Misc.Sp6TransvGen

end
