module

public meta import Lean
meta import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoData
meta import Certificates.Data.FF81Am6A2
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoCodes

namespace CFSG.KD.Sp6A2.Gen

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2Data
  CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

meta def pkM (m : List Nat) : Nat := m.foldr (fun e acc => e + 2 * acc) 0

meta def mulM (A B : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:6] do
    let a := (A >>> (6 * i)) &&& 63
    let mut row := 0
    for k in [0:6] do
      if (a >>> k) &&& 1 == 1 then
        row := row ^^^ ((B >>> (6 * k)) &&& 63)
    r := r ||| (row <<< (6 * i))
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

meta def recsM (b : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat) : List Nat :=
  let (es, par, C, POS) := b
  let (srt, sri) := sortM es
  let n := es.size
  let f := fun (v : Nat) (i : Nat) => v <<< (40 + 16 * i)
  (List.range (n + 1)).map fun t =>
    let p := par.getD t (0, 0)
    es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 ||| f (sri.getD t 0) 3 |||
      f (C.getD (2 * t) 0) 4 ||| f (C.getD (2 * t + 1) 0) 5 ||| f (POS.getD (2 * t) 0) 6 |||
      f (POS.getD (2 * t + 1) 0) 7

meta def gensL : List (List (List Nat)) :=
  [a2XGens 0, a2XGens 1, a2XGens 2, [a2C0, a2S0], [a2C1, a2S1], [a2C2, a2S2], a2K4Gens,
    a2K2Gens, a2DGens, c7P.map Prod.fst]

meta def searchM (g : List (List Nat)) (fuel : Nat) :
    Array Nat × Array (Nat × Nat) × Array Nat × Array Nat :=
  let ga := (g.map pkM).toArray
  bfsM (pkM one6) (fun x s => mulM x ga[s]!) 2 fuel

meta def gaM : Array Nat := #[pkM aC, pkM bC]
meta def gbM : Array Nat := #[pkM aI, pkM bI]

meta def orbM (t : List Nat) : Array Nat :=
  (bfsM (pkM t) (fun x s => mulM (mulM gaM[s]! x) gbM[s]!) 2 4000).1

meta def z7M : Nat := pkM a2Z7

meta def threeM (w : Nat) : Bool := w != pkM one6 && mulM (mulM w w) w == pkM one6

meta def xTabs : Array (Array Nat) :=
  #[(searchM (a2XGens 0) 24000).1, (searchM (a2XGens 1) 24000).1, (searchM (a2XGens 2) 24000).1]

meta def tabStart : Nat := 23 + 63 + 315 + 945 + 3780

meta def tabsM : List Nat := gensL.flatMap fun g => recsM (searchM g 24000)

meta def hitsM : List Nat :=
  ([t0C, t1C, t2C, t3C].flatMap fun t => (orbM t).toList).filter fun x => threeM (mulM z7M x)

meta def capsM : List Nat → Nat → List Nat × List (Nat × Nat)
  | [], _ => ([], [])
  | x :: xs, o =>
    let b := bfsM (pkM one6) (fun y s => mulM y (#[z7M, x])[s]!) 2 168
    let n := b.1.size
    let (xi, pos) := Id.run do
      let mut r := (0, 0)
      for i in [0:3] do
        match xTabs[i]!.idxOf? x with
        | some p => r := (i, p)
        | none => pure ()
      return r
    let d := (o + 2) ||| (n <<< 20) ||| (xi <<< 30) ||| (pos <<< 32)
    let rs := [z7M, x] ++ recsM b
    let (rest, ds) := capsM xs (o + rs.length)
    (rs ++ rest, (x, d) :: ds)

meta def headM : List Nat :=
  gensL.flatMap (fun g => g.map pkM) ++ [tabStart, tabStart + 169, tabStart + 338]

meta def capStart : Nat := tabStart + tabsM.length

meta def recM : List Nat :=
  let (cs, ds) := capsM hitsM capStart
  let dirM := [t0C, t1C, t2C, t3C].flatMap fun t => (orbM t).toList.map fun x =>
    (ds.find? (·.1 == x)).elim 0 (·.2)
  headM ++ dirM ++ tabsM ++ cs ++
    ([vecCode 1 1 0, vecCode 2 2 0, vecCode 0 0 1, vecCode 0 0 2, vecCode 1 1 1, vecCode 2 2 2,
      vecCode 1 1 2, vecCode 2 2 1, fl2C].map pkM)

end CFSG.KD.Sp6A2.Gen

#kss_ntree CFSG.KD.Sp6A2.REC CFSG.KD.Sp6A2.Gen.recM
