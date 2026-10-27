module

public meta import Lean
meta import CFSG.Quasithin.H13.L32NKGConjInputs
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

namespace CFSG.KD.G22C.Gen

open CFSG.Quasithin.H13.KGCert

meta def c64 (x : List Nat) : Nat := (x ++ [64, 128]).foldr (fun c acc => c + 256 * acc) 0

meta def mulM (A B : Nat) : Nat := Id.run do
  let mut r := 0
  for j in [0:8] do
    let b := (B >>> (8 * j)) &&& 255
    let mut col := 0
    for i in [0:8] do
      if (b >>> i) &&& 1 == 1 then
        col := col ^^^ ((A >>> (8 * i)) &&& 255)
    r := r ||| (col <<< (8 * j))
  return r

meta def gA : Nat := c64 gAc
meta def gB : Nat := c64 gBc
meta def oneM : Nat := c64 oneC

meta def esM : Array Nat := Id.run do
  let mut es : Array Nat := #[oneM]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert oneM 0
  let mut fr : List Nat := [0]
  for _ in [0:200] do
    if fr.isEmpty then break
    let mut nf : List Nat := []
    for t in fr do
      for g in [gA, gB] do
        let y := mulM g es[t]!
        if !idx.contains y then
          idx := idx.insert y es.size
          nf := es.size :: nf
          es := es.push y
    fr := nf
  return es

meta def idxM : Std.HashMap Nat Nat :=
  esM.foldl (fun (m : Std.HashMap Nat Nat × Nat) x => (m.1.insert x m.2, m.2 + 1))
    (({} : Std.HashMap Nat Nat), 0) |>.1

meta def posOf (x : Nat) : Nat := idxM.getD x 65535

meta def invM (x : Nat) : Nat := Id.run do
  let mut p := oneM
  for _ in [0:20] do
    if mulM p x == oneM then return p
    p := mulM p x
  return 0

meta def isInvM (x : Nat) : Bool := mulM x x == oneM && x != oneM

meta def t0M : Nat := c64 t0C
meta def t1M : Nat := c64 t1C

meta def conjM : Std.HashMap Nat (Nat × Nat × Nat) := Id.run do
  let mut m : Std.HashMap Nat (Nat × Nat × Nat) := {}
  for (T, cl) in [(t0M, 0), (t1M, 1)] do
    let mut fr : List (Nat × Nat) := [(T, oneM)]
    if !m.contains (posOf T) then
      m := m.insert (posOf T) (posOf oneM, posOf oneM, cl)
    for _ in [0:400] do
      if fr.isEmpty then break
      let mut nf : List (Nat × Nat) := []
      for (z, w) in fr do
        for g in [gA, gB] do
          let z' := mulM (mulM g z) (invM g)
          let p := posOf z'
          if !m.contains p then
            let w' := mulM g w
            m := m.insert p (posOf (invM w'), posOf w', cl)
            nf := (z', w') :: nf
      fr := nf
  return m

meta def clsM (T : Nat) : List Nat :=
  (List.range esM.size).filterMap fun t =>
    let x := esM[t]!
    if isInvM x && mulM T x == mulM x T then some x else none

meta def recM : List Nat :=
  let n := esM.size
  let rows := (List.range n).map fun t =>
    match conjM.get? t with
    | some (y, y', cl) => y ||| (y' <<< 16) ||| (cl <<< 32)
    | none => 0
  let L0 := clsM t0M
  let L1 := clsM t1M
  rows ++ [posOf t0M, posOf t1M, L0.length, L1.length] ++ L0 ++ L1

end CFSG.KD.G22C.Gen

#kss_ntree CFSG.KD.G22C.CR CFSG.KD.G22C.Gen.recM
