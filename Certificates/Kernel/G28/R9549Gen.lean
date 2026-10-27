module

public meta import Certificates.Data.Item434G28R
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

namespace CFSG.KC.G28RGen

open CFSG.RankThree.PartTwo.Sec4.Item434G28

meta def gs : Array Nat := rGens.toArray

meta def gL : List Nat := rGens

meta def idxOf (E : Array Nat) : Std.HashMap Nat Nat :=
  (List.range E.size).foldl (fun m t => m.insert E[t]! t) {}

meta def parents (E : Array Nat) : Array Nat := Id.run do
  let idx := idxOf E
  let mut par : Array Nat := Array.replicate E.size 0
  let mut done : Array Bool := (Array.replicate E.size false).set! 0 true
  for p in [0:E.size] do
    for l in [0:gs.size] do
      let t := idx.getD (mul2 E[p]! gs[l]!) 0
      if t > p && !done[t]! then
        par := par.set! t (p + 2 ^ 24 * l)
        done := done.set! t true
  return par

meta def closL (E : Array Nat) : List Nat :=
  let idx := idxOf E
  (List.range E.size).flatMap fun k => gs.toList.map fun g => idx.getD (mul2 E[k]! g) 0

meta def invols (E : Array Nat) : Array Nat :=
  E.filter fun s => s != id2 && mul2 s s == id2

meta def ord3s (E : Array Nat) : Array Nat :=
  E.filter fun s => s != id2 && pw2 s 3 == id2

meta def inverse (s : Nat) : Nat := Id.run do
  let mut x := s
  for _ in [0:24] do
    if mul2 x s == id2 then return x
    x := mul2 x s
  return 0

meta def invData (E : Array Nat) : Array Nat × Std.HashMap Nat (Nat × Nat × Nat) := Id.run do
  let idx := idxOf E
  let I0 := invols E
  let invs := E.map inverse
  let classOf (rep : Nat) : Std.HashMap Nat (Nat × Nat) := Id.run do
    let mut m : Std.HashMap Nat (Nat × Nat) := {}
    for a in [0:E.size] do
      let g := E[a]!
      let h := invs[a]!
      let t := mul2 (mul2 h rep) g
      if !m.contains t then m := m.insert t (a, idx.getD h 0)
    return m
  let r0 := I0[0]!
  let c0 := classOf r0
  let r1 := (I0.filter fun t => !c0.contains t)[0]!
  let c1 := classOf r1
  let I := #[r0, r1] ++ I0.filter fun t => t != r0 && t != r1
  let mut cj : Std.HashMap Nat (Nat × Nat × Nat) := {}
  for t in I do
    match c0.get? t with
    | some (a, b) => cj := cj.insert t (a, b, 0)
    | none => match c1.get? t with
      | some (a, b) => cj := cj.insert t (a, b, 1)
      | none => pure ()
  return (I, cj)

meta def bfs : Array Nat := Id.run do
  let mut E : Array Nat := #[id2]
  let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert id2
  let mut p := 0
  while p < E.size do
    for g in gs do
      let c := mul2 E[p]! g
      if !seen.contains c then
        E := E.push c
        seen := seen.insert c
    p := p + 1
  return E

meta def eL : List Nat := bfs.toList

meta def pL : List Nat := (parents bfs).toList

meta def cL : List Nat := closL bfs

meta def iL : List Nat := (invData bfs).1.toList

meta def tL : List Nat := (ord3s bfs).toList

meta def ccL : List Nat :=
  let I := (invData bfs).1
  let T := ord3s bfs
  [0, 1].flatMap fun r =>
    (T.filter fun e => mul2 I[r]! e == mul2 e I[r]!).toList

meta def wL : List Nat :=
  let (I, cj) := invData bfs
  let T := ord3s bfs
  let iIdx := idxOf I
  let tIdx := idxOf T
  bfs.toList.map fun s =>
    let ii := iIdx.getD s 0
    let ti := tIdx.getD s 0
    let (a, b, r) := cj.getD s (0, 0, 0)
    ii + 2 ^ 10 * ti + 2 ^ 20 * a + 2 ^ 35 * b + 2 ^ 50 * r

end CFSG.KC.G28RGen

end
