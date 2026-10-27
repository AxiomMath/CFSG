module

public meta import Lean
meta import Certificates.Data.RudvalisFF81Sp8Norm
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
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

namespace CFSG.KD.Sp8N0.Gen

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

meta def c64 (x : List Nat) : Nat := x.foldr (fun c acc => c + 256 * acc) 0

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

meta def bfsM (start : Nat) (st : Nat → Nat → Nat) (k fuel : Nat) :
    Array Nat × Array (Nat × Nat) × Array Nat × Array Nat := Id.run do
  let mut es : Array Nat := #[start]
  let mut par : Array (Nat × Nat) := #[]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert start 0
  let mut C : Array Nat := #[]
  let mut POS : Array Nat := #[]
  for h in [0:fuel] do
    if h < es.size then
      for s in [0:k] do
        C := C.push es.size
        let y := st es[h]! s
        match idx.get? y with
        | some p => POS := POS.push p
        | none =>
          POS := POS.push es.size
          idx := idx.insert y es.size
          es := es.push y
          par := par.push (h, s)
  C := C.push es.size
  return (es, par, C, POS)

meta def sortM (xs : Array Nat) : Array Nat × Array Nat :=
  let srt := (Array.range xs.size).qsort (fun a b => xs[a]! < xs[b]!)
  let sri := (Array.range srt.size).foldl (fun acc i => acc.set! srt[i]! i)
    (Array.replicate srt.size 0)
  (srt, sri)

meta def recsM (k : Nat) (b : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat) : List Nat :=
  let (es, par, C, POS) := b
  let (srt, sri) := sortM es
  let n := es.size
  let f := fun (v : Nat) (i : Nat) => v <<< (64 + 16 * i)
  (List.range (n + 1)).map fun t =>
    let p := par.getD t (0, 0)
    let base := es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 ||| f (sri.getD t 0) 3
    (List.range k).foldl (fun acc s =>
      acc ||| f (C.getD (k * t + s) 0) (4 + s) ||| f (POS.getD (k * t + s) 0) (4 + k + s)) base

meta def unpackL (X : Nat) : List Nat := (List.range 8).map fun j => (X >>> (8 * j)) &&& 255

meta def invM (X : Nat) : Nat := c64 (invS (unpackL X))

meta def gM : Array Nat := (n0Gens.map c64).toArray
meta def zM : Array Nat := (e0Gens.map c64).toArray
meta def oneN : Nat := c64 CFSG.Quasithin.H13.Mat8Cert.one8

meta def tabT : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat :=
  bfsM oneN (fun x s => mulM x gM[s]!) 4 31104

meta def tE : Array Nat :=
  (bfsM oneN (fun x s => mulM x ((pGens.map c64).toArray)[s]!) 4 81).1

meta def tT : Array Nat := tabT.1
meta def tI : Array Nat := tT.map invM

meta def cmapM (a : Nat) : Std.HashMap Nat Nat :=
  (List.range tT.size).foldr (fun t m => m.insert (mulM (mulM tT[t]! a) tI[t]!) t) {}

meta def l1M : Array Nat := (l1S.map c64).toArray
meta def zzM : Nat := c64 zzS
meta def repM : Array Nat := #[0, zM[3]!, mulM zM[3]! zM[3]!, zzM, c64 z012S, c64 z0123S]
meta def mapsM : Array (Std.HashMap Nat Nat) := repM.map cmapM

meta def clsM : List Nat := tE.toList.map fun x =>
  if x == oneN then 0 else
    let r := (List.range 5).findSome? fun c =>
      (mapsM[c + 1]!.get? x).map fun t =>
        let j := (l1M.findIdx? (· == x)).getD 0
        (c + 1) + 8 * j + 64 * t
    r.getD 0

meta def prodM : List Nat := (List.range 64).map fun i =>
  let a := i / 8
  let b := i % 8
  if a / 2 == b / 2 then 0 else (mapsM[3]!.get? (mulM l1M[a]! l1M[b]!)).getD 0

meta def normMap : Std.HashMap (List Nat) Nat :=
  (List.range tT.size).foldr (fun t m =>
    m.insert (zM.toList.map fun z => mulM (mulM tT[t]! z) tI[t]!) t) {}

meta def normM : List Nat := (List.range 4096).map fun q =>
  let key := [l1M[q / 512]!, l1M[q / 64 % 8]!, l1M[q / 8 % 8]!, l1M[q % 8]!]
  (normMap.get? key).getD 0

meta def posM : List Nat := zM.toList.map fun z => (tT.findIdx? (· == z)).getD 0

meta def conjM : List Nat := (List.range 16).map fun i =>
  let g := gM[i / 4]!
  let y := mulM (mulM g zM[i % 4]!) (invM g)
  (tE.findIdx? (· == y)).getD 0

meta def recM : List Nat :=
  gM.toList ++ zM.toList ++ [zzM, c64 z012S, c64 z0123S, mulM zM[3]! zM[3]!] ++ posM ++
    recsM 4 tabT ++ clsM ++ prodM ++ normM ++ gM.toList.map invM ++ conjM

end CFSG.KD.Sp8N0.Gen

#kss_ntree CFSG.KD.Sp8N0.REC CFSG.KD.Sp8N0.Gen.recM
