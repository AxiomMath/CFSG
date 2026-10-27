module

public meta import Lean
meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43CoverCheck
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

namespace CFSG.KD.U43P.Gen

open CFSG.RankThree.PartTwo.Sec4.Item434RemU43

meta def fmP (c : List Nat) : Nat :=
  (List.range c.length).foldl (fun acc m =>
    acc + ((c.getD m 0 / 3) <<< (16 * m)) + ((c.getD m 0 % 3) <<< (256 + 16 * m))) 0

meta def pk (fs : List Nat) : Nat := fs.foldr (fun f acc => f + (acc <<< 10)) 0

meta def sqL : List Nat := (List.range 729).map fun t => fmP (sq4 (uAt t))
meta def kndL : List Nat := uKind
meta def caL : List Nat := (List.range 729).map fun q => fmP (wordCode (convRWord q))
meta def cbL : List Nat := (List.range 729).map fun q => fmP (wordCode (invWord (convRWord q)))
meta def olL : List Nat := (List.range 729).filter isOrd3
meta def oliL : List Nat :=
  ((List.range olL.length).foldl (fun acc j => acc.set! (olL.getD j 0) j)
    (Array.replicate 729 0)).toList

meta def witM : List Nat × List Nat := Id.run do
  let es := uElems
  let idx : Std.HashMap (List Nat) Nat :=
    (List.range es.size).foldl (fun m t => m.insert es[t]! t) {}
  let pos := fun (c : List Nat) => idx.getD c 729
  let rts : Std.HashSet Nat := uRt.foldl (fun s r => s.insert r) {}
  let inR := fun (c : List Nat) => rts.contains (pos c)
  let kinds := uKind.toArray
  let cps : Array (List Nat × List Nat) := (Array.range 729).map fun q =>
    (wordCode (convRWord q), wordCode (invWord (convRWord q)))
  let cj := fun (q : Nat) (x : List Nat) => mul4 (mul4 (cps[q]!).1 x) (cps[q]!).2
  let z1 := uAt uZ
  let z2 := sq4 z1
  let bA : Array (List Nat) := (Array.range 12).map fun k => uAt ((badTriple k).getD 1 0)
  let bB : Array (List Nat) := (Array.range 12).map fun k => uAt ((badTriple k).getD 2 0)
  let yG : Array (List Nat) := (Array.range 39).map fun m => uAt ((yTriple (m / 3)).getD (m % 3) 0)
  let ol := olL.toArray
  let mut wp : Array Nat := Array.replicate (296 * 296) 0
  let mut wc : Array Nat := Array.replicate (296 * 296) 0
  for j₁ in [0:296] do
    for j₂ in [0:296] do
      let ia := ol[j₁]!
      let ib := ol[j₂]!
      let a := es[ia]!
      let b := es[ib]!
      if ia < ib && mul4 a b == mul4 b a then
        let a2 := sq4 a
        let b2 := sq4 b
        let za := [one4, z1, z2].flatMap fun x => [one4, a, a2].map fun y => mul4 x y
        let els : Array (List Nat) := (za.flatMap fun u => [u, mul4 u b, mul4 u b2]).toArray
        let w : Nat := Id.run do
          if a == z1 || a == z2 then return pk [1]
          match (List.range 9).find? (fun m => za.getD m [] == b) with
          | some m => return pk [2, m]
          | none =>
            match (List.range 27).find? (fun e => e != 0 && kinds[pos els[e]!]!  == 2) with
            | some x =>
              let qx := pos els[x]!
              let ok := fun (u : Nat) => els[u]! != one4 && inR (cj qx els[u]!)
              let okv := fun (u v : Nat) => ok v && els[v]! != els[u]! && els[v]! != sq4 els[u]!
              match (List.range 27).find? (fun u => ok u && (List.range 27).any (okv u)) with
              | some u =>
                let v := ((List.range 27).find? (okv u)).getD 0
                return pk ([3, x, u, v, pos (cj qx els[u]!), pos (cj qx els[v]!)] ++
                  (List.range x).map fun i => pos els[i + 1]!)
              | none => pure ()
            | none => pure ()
            match (List.range 12).find? (fun k => els.contains bA[k]! && els.contains bB[k]!) with
            | some k =>
              let ea := ((List.range 27).find? (fun e => els[e]! == bA[k]!)).getD 0
              let eb := ((List.range 27).find? (fun e => els[e]! == bB[k]!)).getD 0
              return pk [4, k, ea, eb]
            | none => return 0
        let e9 : Array (List Nat) :=
          ([one4, a, a2].flatMap fun x => [one4, b, b2].map fun y => mul4 x y).toArray
        let v : Nat := Id.run do
          if b == a2 then return pk [1]
          let ok1 := fun (t : Nat) => e9[t + 1]! != one4 && inR (cj (pos e9[t + 1]!) e9[t + 1]!)
          match (List.range 8).find? ok1 with
          | some t => return pk [2, t, pos e9[t + 1]!, pos (cj (pos e9[t + 1]!) e9[t + 1]!)]
          | none => pure ()
          let okt := fun (n i t : Nat) =>
            e9[t + 1]! != one4 && mul4 yG[3 * n + i]! e9[t + 1]! == mul4 e9[t + 1]! yG[3 * n + i]!
          match (List.range 13).find? (fun n => (List.range 3).all fun i =>
              (List.range 8).any (okt n i)) with
          | some n =>
            let ts := (List.range 3).map fun i => ((List.range 8).find? (okt n i)).getD 0
            return pk ([3, n] ++ ts ++ ts.map fun t => pos e9[t + 1]!)
          | none => return 0
        wp := wp.set! (296 * j₁ + j₂) w
        wc := wc.set! (296 * j₁ + j₂) v
  return (wp.toList, wc.toList)

meta def wpL : List Nat := witM.1
meta def wcL : List Nat := witM.2

meta def yrL : List Nat := (List.range 39).map fun m =>
  let n := m / 3
  let c := conjStep (wordPair (yWord n)) (uAt ((yTriple n).getD (m % 3) 0))
  ((List.range 729).find? (fun t => uAt t == c)).getD 729

end CFSG.KD.U43P.Gen

#kss_ntree CFSG.KD.U43P.SQP CFSG.KD.U43P.Gen.sqL
#kss_ntree CFSG.KD.U43P.KND CFSG.KD.U43P.Gen.kndL
#kss_ntree CFSG.KD.U43P.CAP CFSG.KD.U43P.Gen.caL
#kss_ntree CFSG.KD.U43P.CBP CFSG.KD.U43P.Gen.cbL
#kss_ntree CFSG.KD.U43P.OL CFSG.KD.U43P.Gen.olL
#kss_ntree CFSG.KD.U43P.OLI CFSG.KD.U43P.Gen.oliL
#kss_ntree CFSG.KD.U43P.WP CFSG.KD.U43P.Gen.wpL
#kss_ntree CFSG.KD.U43P.WC CFSG.KD.U43P.Gen.wcL
#kss_ntree CFSG.KD.U43P.YR CFSG.KD.U43P.Gen.yrL
