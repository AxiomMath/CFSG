module

public meta import Lean
meta import Certificates.Data.YamakiPres
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

namespace CFSG.KD.YamakiLbar.Gen

open CFSG.ClassicalInvolution.Solomon73.Yamaki

meta def numM (i : Fin 12) : Nat :=
  (List.finRange 6).foldl (fun acc r => (List.finRange 6).foldl (fun acc c =>
    acc ||| ((yamakiMat6 i r c).val <<< (6 * r.val + c.val))) acc) 0

meta def mulM (A B : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:6] do
    let mut row := 0
    for k in [0:6] do
      if (A >>> (6 * i + k)) &&& 1 == 1 then
        row := row ^^^ ((B >>> (6 * k)) &&& 63)
    r := r ||| (row <<< (6 * i))
  return r

meta def bfsM (start : Nat) (st : Nat → Nat → Nat) (k fuel : Nat) :
    Array Nat × Array (Nat × Nat) × Array Nat × Array Nat × Std.HashMap Nat Nat := Id.run do
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
  return (es, par, C, POS, idx)

meta def sortM (xs : Array Nat) : Array Nat × Array Nat :=
  let srt := (Array.range xs.size).qsort (fun a b => xs[a]! < xs[b]!)
  let sri := (Array.range srt.size).foldl (fun acc i => acc.set! srt[i]! i)
    (Array.replicate srt.size 0)
  (srt, sri)

meta def recsM (k : Nat)
    (b : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat × Std.HashMap Nat Nat) :
    List Nat :=
  let (es, par, C, POS, _) := b
  let (srt, sri) := sortM es
  let n := es.size
  let f := fun (v : Nat) (i : Nat) => v <<< (64 + 16 * i)
  (List.range (n + 1)).map fun t =>
    let p := par.getD t (0, 0)
    let base := es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 |||
      f (sri.getD t 0) 3
    (List.range k).foldl (fun acc s =>
      acc ||| f (C.getD (k * t + s) 0) (4 + s) ||| f (POS.getD (k * t + s) 0) (4 + k + s)) base

meta def gM : Array Nat := ((List.finRange 12).map numM).toArray

meta def oneM : Nat := 34630287489

meta def tabA : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat × Std.HashMap Nat Nat :=
  bfsM oneM (fun x s => mulM x gM[s + 3]!) 6 64

meta def crdM : Array Nat :=
  tabA.2.1.foldl (fun acc p => acc.push (acc[p.1]! ^^^ (1 <<< p.2))) #[0]

meta def pscM : Array Nat :=
  (Array.range 64).foldl (fun acc k => acc.set! crdM[k]! k) (Array.replicate 64 0)

meta def nM (i : Nat) : Nat :=
  (List.range 6).foldl (fun acc j =>
    let y := mulM (mulM gM[i]! gM[j + 3]!) gM[i]!
    acc ||| (crdM[(tabA.2.2.2.2.get? y).getD 0]! <<< (6 * j))) 0

meta def nsM : Array Nat := ((List.range 11).map nM).toArray

meta def lgM : Array Nat := #[nsM[0]!, mulM nsM[10]! nsM[9]!]

meta def tabL : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat × Std.HashMap Nat Nat :=
  bfsM oneM (fun x s => mulM lgM[s]! x) 2 168

meta def lM : Array Nat := tabL.1

meta def posL (x : Nat) : Nat := (tabL.2.2.2.2.get? x).getD 0

meta def iaM : Array Nat := (Array.range 168).filter fun t => mulM lM[t]! lM[t]! == oneM

meta def ibM : Array Nat :=
  (Array.range 168).filter fun t => mulM (mulM lM[t]! lM[t]!) lM[t]! == oneM

meta def invIdx (xs : Array Nat) : List Nat :=
  (List.range 168).map fun t => (xs.findIdx? (· == t)).getD 0

meta def invM (t : Nat) : Nat := posL ((List.range 168).foldl (fun acc u =>
  if mulM lM[t]! lM[u]! == oneM then lM[u]! else acc) 0)

meta def orbM : Array Nat × Array (Nat × Nat) := Id.run do
  let mut reps : Array Nat := #[]
  let mut cov : Array (Option (Nat × Nat)) := Array.replicate 64 none
  for c in [1:64] do
    if cov[c]!.isNone then
      let ri := reps.size
      reps := reps.push c
      for t in [0:168] do
        let w := mulM c lM[t]!
        if cov[w]!.isNone then
          cov := cov.set! w (some (ri, t))
  return (reps, cov.map fun o => o.getD (0, 0))

meta partial def lamM (ta tb m : Nat) : Nat :=
  if m == 0 then oneM else
    let p := tabL.2.1[m - 1]!
    mulM (if p.2 == 0 then ta else tb) (lamM ta tb p.1)

meta def z6JM : List (List Nat) := [[0, 5, 14], [0, 2, 3], [0], [2, 5, 8], [2], [5]]

meta def gmatM (ta tb r : Nat) : Nat :=
  ((z6JM.map fun J => J.foldl (fun a m => a ^^^ mulM r (lamM ta tb m)) 0).zipIdx).foldl
    (fun acc (row, j) => acc ||| (row <<< (6 * j))) 0

meta def witM (i : Nat) : Nat :=
  let ta := lM[iaM[i / 228]!]!
  let tb := lM[ibM[(i / 4) % 57]!]!
  let r := orbM.1[i % 4]!
  let G := gmatM ta tb r
  if mulM lgM[0]! G == mulM G ta && mulM lgM[1]! G == mulM G tb then
    match tabL.2.2.2.2.get? G with
    | some p => 1 + p
    | none => 1000 + ((List.range 64).find? fun x => x != 0 && mulM x G == 0).getD 0
  else 0

meta def qM : List Nat :=
  nsM.toList ++ [lgM[1]!] ++ crdM.toList ++ pscM.toList ++ recsM 2 tabL ++
    nsM.toList.map posL ++ iaM.toList ++ ibM.toList ++ invIdx iaM ++ invIdx ibM ++
    orbM.1.toList ++ orbM.2.toList.map (·.1) ++
    orbM.2.toList.map (fun p => invM p.2) ++ orbM.2.toList.map (·.2)

meta def wM : List Nat := (List.range 5016).map witM

end CFSG.KD.YamakiLbar.Gen

#kss_ntree CFSG.KD.YamakiLbar.QREC CFSG.KD.YamakiLbar.Gen.qM
#kss_ntree CFSG.KD.YamakiLbar.WREC CFSG.KD.YamakiLbar.Gen.wM
