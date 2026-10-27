module

public meta import Lean
meta import Certificates.Data.Foote82OmegaSixClass
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.OmegaSix.GenO

open CFSG.CGT.Foote82.OmegaSix CFSG.KD.YamakiRep.Gen

meta def coordsO : List (Fin 2 ⊕ Fin 2 ⊕ Fin 2) :=
  [.inl 0, .inl 1, .inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1)]

meta def numOO (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) : Nat :=
  coordsO.foldl (fun acc a => coordsO.foldl (fun acc b =>
    acc ||| ((A a b).val <<< (6 * (bit6 a).val + (bit6 b).val))) acc) 0

meta def recT (gs : List Nat) (n : Nat) : List Nat :=
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

meta def recOO : List Nat := recT [numOO aMat, numOO bMat, numOO rMat] 51840

end CFSG.KD.OmegaSix.GenO

#kss_ntree CFSG.KD.OmegaSix.ROO CFSG.KD.OmegaSix.GenO.recOO
