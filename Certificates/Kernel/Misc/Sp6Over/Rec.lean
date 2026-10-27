module

public meta import Lean
meta import Certificates.Data.RudvalisFF81Sp6Over
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public meta import CFSG.Certificates.Kernel.Common.Eval
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

namespace CFSG.KD.Sp6Over.Gen

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over CFSG.Quasithin.H13.MatNCert
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

meta def cp (n : Nat) (x : List Nat) : Nat := x.foldr (fun c acc => c + 2 ^ n * acc) 0

meta def bitM (x i : Nat) : Nat := (x >>> i) &&& 1

meta def pairs : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5),
    (3, 4), (3, 5), (4, 5)]

meta def basImg (g : List Nat) (i j : Nat) : Nat :=
  let G := fun r a => bitM (g.getD a 0) r
  pairs.zipIdx.foldl (fun acc x =>
    acc ||| (((G i x.1.1 * G j x.1.2 + G j x.1.1 * G i x.1.2) % 2) <<< x.2)) 0

meta def imgs (g : List Nat) : Array Nat := (pairs.map fun ij => basImg g ij.1 ij.2).toArray

meta def actM (im : Array Nat) (c : Nat) : Nat :=
  (List.range 15).foldl (fun acc p => if bitM c p == 1 then acc ^^^ im[p]! else acc) 0

meta def code15 (w : List Nat) : Nat :=
  pairs.zipIdx.foldl (fun acc x => acc ||| (bitM (w.getD x.1.2 0) x.1.1 <<< x.2)) 0

meta def invM (g : List Nat) : List Nat := Id.run do
  let mut p := g
  let mut prev := oneN 6
  for _ in [0:64] do
    if p == oneN 6 then return prev
    prev := p
    p := mulN p g
  return oneN 6

meta def recsOf (gs : Array (Array Nat)) (root : Nat) : Array Nat := Id.run do
  let mut es : Array Nat := #[root]
  let mut par : Array (Nat × Nat) := #[(0, 0)]
  let mut dep : Array Nat := #[0]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert root 0
  for h in [0:20000] do
    if h < es.size then
      for s in [0:gs.size] do
        let y := actM gs[s]! es[h]!
        if !idx.contains y then
          idx := idx.insert y es.size
          es := es.push y
          par := par.push (h, s)
          dep := dep.push (dep[h]! + 1)
  let mut ch : Array (Array Nat) := Array.replicate es.size #[]
  for t in [1:es.size] do
    ch := ch.modify par[t]!.1 (·.push t)
  let mut out : Array Nat := #[]
  let mut st : Array Nat := #[0]
  for _ in [0:es.size] do
    match st.back? with
    | none => pure ()
    | some t =>
      st := st.pop
      out := out.push (if t == 0 then 0 else dep[t]! + 64 * par[t]!.2)
      for c in ch[t]!.reverse do
        st := st.push c
  return out

meta def encRel (r : List Nat × Nat) : Nat :=
  r.2 + 16 * r.1.length + 256 * r.1.foldr (fun d acc => d + 4 * acc) 0

meta def mats : List (List Nat) := sbGens ++ grs

meta def encW (w : List Nat) : Nat := w.length + 16 * w.foldr (fun d acc => d + 4 * acc) 0

meta def pkM (m : List Nat) : Nat := m.foldr (fun e acc => e + 2 * acc) 0

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

meta def recsM (k : Nat) (b : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat) :
    List Nat :=
  let (es, par, C, POS) := b
  let (srt, sri) := sortM es
  let n := es.size
  let f := fun (v : Nat) (i : Nat) => v <<< (64 + 16 * i)
  (List.range (n + 1)).map fun t =>
    let p := par.getD t (0, 0)
    let base := es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 ||| f (sri.getD t 0) 3
    (List.range k).foldl (fun acc s =>
      acc ||| f (C.getD (k * t + s) 0) (4 + s) ||| f (POS.getD (k * t + s) 0) (4 + k + s)) base

meta def mulP (n A B : Nat) : Nat :=
  cp n (mulN ((List.range n).map fun j => (A >>> (n * j)) &&& (2 ^ n - 1))
    ((List.range n).map fun j => (B >>> (n * j)) &&& (2 ^ n - 1)))

meta def kcM (m : Nat) : Nat := cp 7 (kC m)

meta def gpM (x : List Nat) : Array (Nat × Nat) :=
  ((kGps x).map fun gp => (cp 7 (gp.take 7), cp 7 (gp.drop 7))).toArray

meta def kRecs (x : List Nat) : List Nat :=
  let g := gpM x
  let b := bfsM (kcM 1) (fun y s => mulP 7 (mulP 7 g[s]!.1 y) g[s]!.2) 3 64
  let r := recsM 3 b
  r ++ List.replicate (64 - r.length) 0

meta def kWit (x : List Nat) : List Nat :=
  let g := gpM x
  let es := (bfsM (kcM 1) (fun y s => mulP 7 (mulP 7 g[s]!.1 y) g[s]!.2) 3 64).1
  (List.range 64).map fun m => (es.findIdx? (· == kcM m)).getD 0

meta def rRecs (x : List Nat) : List Nat :=
  let g := ((rGens x).map (cp 7)).toArray
  recsM 5 (bfsM (cp 7 (oneN 7)) (fun y s => mulP 7 y g[s]!) 5 64)

meta def uRecs : List Nat :=
  let g := (uGens.map (cp 6)).toArray
  recsM 3 (bfsM (cp 6 (oneN 6)) (fun y s => mulP 6 y g[s]!) 3 64)

meta def recM : List Nat :=
  mats.map (cp 6) ++ mats.map (fun g => cp 6 (invM g)) ++ [code15 w0c] ++
    [nGc, nHc, xSc, xIc].map (cp 7) ++ relW.map encRel ++
    [ovGamC, ovGamI, ovHC, ovHI, ovCC, ovCI].map pkM ++
    [zCode 0, zCode 1, tCode].map pkM ++ sylowP.map (fun p => pkM p.1) ++
    ([wZ0, wZ1, wT] ++ wS ++ [[0, 1, 2], wP1]).map encW ++ uGens.map (cp 6) ++
    kRecs xSc ++ kWit xSc ++ rRecs xSc ++ kRecs xIc ++ kWit xIc ++ rRecs xIc ++ uRecs

meta def walkM : Array Nat :=
  let sb := (sbGens.map imgs).toArray
  let w0 := code15 w0c
  grs.foldl (fun acc g => acc ++ recsOf sb (actM (imgs g) w0)) #[0]

meta def flM : List Nat :=
  let W := walkM
  (List.range ((W.size + 63) / 64)).map fun k =>
    (List.range 64).foldl (fun acc i => acc ||| (W.getD (64 * k + i) 0 <<< (8 * i))) 0

open CFSG.KC.Eval in
meta def flStep : Step := fun _ => return #[(.anonymous, .list (flM.toArray.map fun r => .nat r))]

end CFSG.KD.Sp6Over.Gen

#kss_ntree CFSG.KD.Sp6Over.REC CFSG.KD.Sp6Over.Gen.recM

#kc_eval CFSG.KD.Sp6Over FL CFSG.KD.Sp6Over.Gen.flStep
