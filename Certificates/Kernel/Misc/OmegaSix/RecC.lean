module

public meta import Lean
meta import Certificates.Data.Foote82OmegaSixClass
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.OmegaSix.GenC

open CFSG.CGT.Foote82.OmegaSix CFSG.KD.YamakiRep.Gen

meta def coordsC : List (Fin 2 ⊕ Fin 2 ⊕ Fin 2) :=
  [.inl 0, .inl 1, .inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1)]

meta def numC (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) : Nat :=
  coordsC.foldl (fun acc a => coordsC.foldl (fun acc b =>
    acc ||| ((A a b).val <<< (6 * (bit6 a).val + (bit6 b).val))) acc) 0

meta def gensC : List Nat :=
  let a := numC aMat
  let b := numC bMat
  [a, b, a, mulM b (mulM b (mulM b b))]

meta def conjM (x : Nat) (fuel : Nat) :
    Array Nat × Array (Nat × Nat) × Array Nat × Array Nat := Id.run do
  let g := gensC.toArray
  let mut es : Array Nat := #[x]
  let mut par : Array (Nat × Nat) := #[]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert x 0
  let mut C : Array Nat := #[]
  let mut POS : Array Nat := #[]
  for h in [0:fuel] do
    if h < es.size then
      for s in [0:2] do
        C := C.push es.size
        let y := mulM (mulM g[s]! es[h]!) g[2 + s]!
        match idx.get? y with
        | some p => POS := POS.push p
        | none =>
          POS := POS.push es.size
          idx := idx.insert y es.size
          es := es.push y
          par := par.push (h, s)
  C := C.push es.size
  return (es, par, C, POS)

meta def recC (x n : Nat) : List Nat :=
  let (es, par, C, POS) := conjM x n
  if es.size != n then panic! s!"the orbit has {es.size} elements" else
  let (srt, sri) := sortM es
  let f := fun (v : Nat) (i : Nat) => v <<< (64 + 16 * i)
  gensC ++ [x] ++ (List.range (es.size + 1)).map fun t =>
    let p := par.getD t (0, 0)
    let base := es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 |||
      f (sri.getD t 0) 3
    (List.range 2).foldl (fun acc s =>
      acc ||| f (C.getD (2 * t + s) 0) (4 + s) ||| f (POS.getD (2 * t + s) 0) (6 + s)) base

meta def recA : List Nat := recC (numC rAMat) 45

meta def recB : List Nat := recC (numC rBMat) 270

end CFSG.KD.OmegaSix.GenC

#kss_ntree CFSG.KD.OmegaSix.RCA CFSG.KD.OmegaSix.GenC.recA
#kss_ntree CFSG.KD.OmegaSix.RCB CFSG.KD.OmegaSix.GenC.recB
