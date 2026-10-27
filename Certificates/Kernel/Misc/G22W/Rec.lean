module

public meta import Lean
meta import CFSG.Quasithin.H13.L32NKGCertInputs
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

namespace CFSG.KD.G22W.Gen

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

meta def posM (g t : Nat) : Nat := idxM.getD (mulM g esM[t]!) 65535

meta def invsM : Array Nat :=
  (Array.range esM.size).filter fun t => mulM esM[t]! esM[t]! == oneM && esM[t]! != oneM

meta def mvM (A v : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:6] do
    if (v >>> i) &&& 1 == 1 then
      r := r ^^^ ((A >>> (8 * i)) &&& 255)
  return r

meta def stabM : Array (Array Nat) :=
  (Array.range 64).map fun v => (Array.range esM.size).filter fun γ => mvM esM[γ]! v == v

meta def witM (x v : Nat) : Nat :=
  if v == 0 || mvM x v != v then 0 else
    (stabM[v]!.find? fun γ => mulM esM[γ]! x != mulM x esM[γ]!).getD 16383

meta def recM : List Nat :=
  let n := esM.size
  let srt := (Array.range n).qsort (fun a b => esM[a]! < esM[b]!)
  let sri := (Array.range n).foldl (fun acc i => acc.set! srt[i]! i) (Array.replicate n 0)
  let kOf : Std.HashMap Nat Nat :=
    invsM.foldl (fun (m : Std.HashMap Nat Nat × Nat) t => (m.1.insert t m.2, m.2 + 1))
      (({} : Std.HashMap Nat Nat), 0) |>.1
  let f := fun (v : Nat) (i : Nat) => v <<< (64 + 16 * i)
  let rows := (List.range n).map fun t =>
    esM[t]! ||| f (posM gA t) 0 ||| f (posM gB t) 1 ||| f srt[t]! 2 ||| f sri[t]! 3 |||
      f (kOf.getD t 0) 4
  let wits := invsM.toList.map fun t =>
    (List.range 64).foldl (fun acc v => acc ||| (witM esM[t]! v <<< (14 * v))) 0
  [gA, gB] ++ rows ++ wits

end CFSG.KD.G22W.Gen

#kss_ntree CFSG.KD.G22W.REC CFSG.KD.G22W.Gen.recM
