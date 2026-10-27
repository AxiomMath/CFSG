module

public meta import Lean
public meta import Certificates.Data.Foote82OmegaSixMax
public meta import Certificates.Kernel.Misc.YamakiRep.Gen
public import Certificates.Kernel.Misc.YamakiRep.Gen

public section

namespace CFSG.KD.OmegaSix.GenX

open CFSG.CGT.Foote82.OmegaSix CFSG.KD.YamakiRep.Gen

meta def coordsX : List (Fin 2 ⊕ Fin 2 ⊕ Fin 2) :=
  [.inl 0, .inl 1, .inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1)]

meta def numX (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) : Nat :=
  coordsX.foldl (fun acc a => coordsX.foldl (fun acc b =>
    acc ||| ((A a b).val <<< (6 * (bit6 a).val + (bit6 b).val))) acc) 0

meta def recTX (gs : List Nat) (n : Nat) : List Nat :=
  let (es, par, C, POS) := bfsM gs.toArray n
  if es.size != n then panic! s!"the table has {es.size} elements" else
  let (srt, sri) := sortM es
  let k := gs.length
  let f := fun (v : Nat) (i : Nat) => v <<< (64 + 16 * i)
  gs ++ (List.range (es.size + 1)).map fun t =>
    let p := par.getD t (0, 0)
    let base := es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 |||
      f (sri.getD t 0) 3
    (List.range k).foldl (fun acc s =>
      acc ||| f (C.getD (k * t + s) 0) (4 + s) ||| f (POS.getD (k * t + s) 0) (4 + k + s)) base

meta def invX (x : Nat) : Nat := Id.run do
  let mut p := oneM
  for _ in [0:64] do
    let q := mulM p x
    if q == oneM then return p
    p := q
  panic! "no inverse"

meta def rsX : Nat × Nat × Nat :=
  let r := numX rMat
  let d1 := numX dc1Mat
  let d2 := numX dc2Mat
  (r, mulM (mulM d1 r) d1, mulM (mulM d2 r) d2)

meta def crRecs : List Nat := recTX [numX cr1Mat, numX cr2Mat] 720

meta def hdrX : List Nat :=
  let es := (bfsM #[numX aMat, numX bMat] 25920).1
  let (_, s1, s2) := rsX
  [numX dc1Mat, numX dc2Mat, s1, s2] ++ [cr1Mat, cr2Mat, dc1Mat, dc2Mat].map fun A =>
    (es.findIdx? (· == numX A)).getD 0

meta def witX : List Nat := Id.run do
  let es := (bfsM #[numX aMat, numX bMat] 25920).1
  let cs := (bfsM #[numX cr1Mat, numX cr2Mat] 720).1
  let (r, s1, s2) := rsX
  let mut idx : Std.HashMap Nat Nat := {}
  for w in [0:cs.size] do
    let c := cs[w]!
    let ci := invX c
    for s in [s1, s2] do
      let u := mulM (mulM ci s) c
      if !idx.contains u then idx := idx.insert u w
  let mut out : Array Nat := #[]
  for y in es do
    if mulM y r == mulM r y then out := out.push 0
    else
      match idx.get? (mulM (mulM y r) (invX y)) with
      | some w => out := out.push w
      | none => panic! "no coset witness"
  return out.toList

end CFSG.KD.OmegaSix.GenX

end
