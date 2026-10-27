module

public meta import Lean
meta import Certificates.Data.Foote82OmegaSixCent
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.OmegaSix.GenA

open CFSG.CGT.Foote82.OmegaSix CFSG.KD.YamakiRep.Gen

meta def coordsA : List (Fin 2 ⊕ Fin 2 ⊕ Fin 2) :=
  [.inl 0, .inl 1, .inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1)]

meta def numA (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) : Nat :=
  coordsA.foldl (fun acc a => coordsA.foldl (fun acc b =>
    acc ||| ((A a b).val <<< (6 * (bit6 a).val + (bit6 b).val))) acc) 0

meta def gensA : Array Nat := #[numA aMat, numA bMat, numA rMat]

meta def invsA : Array Nat :=
  let b := numA bMat
  #[numA aMat, mulM b (mulM b (mulM b b)), numA rMat]

meta def bfsA (x fuel : Nat) :
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
        let y := mulM (mulM gensA[s]! es[h]!) invsA[s]!
        match idx.get? y with
        | some p => POS := POS.push p
        | none =>
          POS := POS.push es.size
          idx := idx.insert y es.size
          es := es.push y
          par := par.push (h, s)
  C := C.push es.size
  return (es, par, C, POS)

meta def recA (x n : Nat) : List Nat :=
  let (es, par, C, POS) := bfsA x n
  if es.size != n then panic! s!"the orbit has {es.size} elements" else
  let (srt, sri) := sortM es
  let f := fun (v : Nat) (i : Nat) => v <<< (64 + 16 * i)
  invsA.toList ++ [0, x] ++ (List.range (es.size + 1)).map fun t =>
    let p := par.getD t (0, 0)
    let base := es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 |||
      f (sri.getD t 0) 3
    (List.range 3).foldl (fun acc s =>
      acc ||| f (C.getD (3 * t + s) 0) (4 + s) ||| f (POS.getD (3 * t + s) 0) (7 + s)) base

meta def recRA : List Nat := recA (numA rAMat) 45

meta def recRB : List Nat := recA (numA rBMat) 270

meta def recL : List Nat :=
  let x := numA rBMat
  let es := (bfsM gensA 51840).1
  let cs := (es.filter fun t => t != oneM && mulM t x == mulM x t).qsort (· < ·)
  if cs.size != 191 then panic! s!"the centralizer has {cs.size} elements" else cs.toList

end CFSG.KD.OmegaSix.GenA

#kss_ntree CFSG.KD.OmegaSix.RCA3 CFSG.KD.OmegaSix.GenA.recRA
#kss_ntree CFSG.KD.OmegaSix.RCB3 CFSG.KD.OmegaSix.GenA.recRB
#kss_ntree CFSG.KD.OmegaSix.RL CFSG.KD.OmegaSix.GenA.recL
