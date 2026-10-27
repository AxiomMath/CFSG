module

public meta import Lean
meta import Certificates.Data.Foote82OmegaSixAut
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.OmegaSix.GenF

open CFSG.CGT.Foote82.OmegaSix CFSG.KD.YamakiRep.Gen

meta def coordsF : List (Fin 2 ⊕ Fin 2 ⊕ Fin 2) :=
  [.inl 0, .inl 1, .inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1)]

meta def numF (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) : Nat :=
  coordsF.foldl (fun acc a => coordsF.foldl (fun acc b =>
    acc ||| ((A a b).val <<< (6 * (bit6 a).val + (bit6 b).val))) acc) 0

meta def gensF : Array Nat := #[numF aMat, numF bMat, numF rMat]

meta def invsF : Array Nat :=
  let b := numF bMat
  #[numF aMat, mulM b (mulM b (mulM b b)), numF rMat]

meta def bfsF (x fuel : Nat) :
    Array Nat × Array (Nat × Nat) × Array Nat × Array Nat := Id.run do
  let mut es : Array Nat := #[x]
  let mut par : Array (Nat × Nat) := #[]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert x 0
  let mut C : Array Nat := #[]
  let mut POS : Array Nat := #[]
  for h in [0:fuel] do
    if h < es.size then
      for s in [0:3] do
        C := C.push es.size
        let y := mulM (mulM gensF[s]! es[h]!) invsF[s]!
        match idx.get? y with
        | some p => POS := POS.push p
        | none =>
          POS := POS.push es.size
          idx := idx.insert y es.size
          es := es.push y
          par := par.push (h, s)
  C := C.push es.size
  return (es, par, C, POS)

meta def recOrb (x n : Nat) : List Nat :=
  let (es, par, C, POS) := bfsF x n
  if es.size != n then panic! s!"the orbit has {es.size} elements" else
  let (srt, sri) := sortM es
  let f := fun (v : Nat) (i : Nat) => v <<< (64 + 16 * i)
  invsF.toList ++ [0, x] ++ (List.range (es.size + 1)).map fun t =>
    let p := par.getD t (0, 0)
    let base := es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 |||
      f (sri.getD t 0) 3
    (List.range 3).foldl (fun acc s =>
      acc ||| f (C.getD (3 * t + s) 0) (4 + s) ||| f (POS.getD (3 * t + s) 0) (7 + s)) base

meta def recRF : List Nat := recOrb (numF bMat) 5184

meta def wordXY (x y : Nat) (w : List Nat) : Nat :=
  w.foldr (fun i acc => mulM (if i == 0 then x else y) acc) oneM

meta def recPW : List Nat :=
  let a := gensF[0]!
  let b := gensF[1]!
  let om := (bfsM #[a, b] 25920).1
  let oo := (bfsM gensF 51840).1
  let xs := om.toList.filter fun x => x != oneM && relators.all fun w => wordXY x b w == oneM
  if xs.length != 10 then panic! s!"{xs.length} pairs" else
  xs.map fun x =>
    match (List.range oo.size).find? (fun j =>
        mulM oo[j]! b == mulM b oo[j]! && mulM oo[j]! a == mulM x oo[j]!) with
    | some j => x ||| (j <<< 36)
    | none => panic! "no witness"

end CFSG.KD.OmegaSix.GenF

#kss_ntree CFSG.KD.OmegaSix.RCF CFSG.KD.OmegaSix.GenF.recRF
#kss_ntree CFSG.KD.OmegaSix.PWF CFSG.KD.OmegaSix.GenF.recPW
