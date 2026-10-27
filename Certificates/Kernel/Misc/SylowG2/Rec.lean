module

public meta import Lean
meta import Certificates.Data.Foote82SylowG2
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen
import Mathlib.Data.FunLike.Basic

namespace CFSG.KD.SylowG2.Gen

open CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIG2Aux CFSG.KD.YamakiRep.Gen

meta def coordsS : List (Fin 2 ⊕ Fin 2 ⊕ Fin 2) :=
  [.inl 0, .inl 1, .inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1)]

meta def numS (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) : Nat :=
  coordsS.foldl (fun acc a => coordsS.foldl (fun acc b =>
    acc ||| ((A a b).val <<< (6 * (bit6 a).val + (bit6 b).val))) acc) 0

meta def recS (gs : List Nat) (n : Nat) : List Nat :=
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

meta def encS (l : List Nat) : Nat := l.foldr (fun a acc => a + 16 * acc) 0

meta def compS (p q : List Nat) : List Nat := q.map fun j => p.getD j 0

meta def imgS (gs : List Nat) (n : Nat) (sig : Array (List Nat)) : List Nat := Id.run do
  let (es, par, _, _) := bfsM gs.toArray n
  let mut P : Array (List Nat) := #[List.range (sig[0]!).length]
  for t in [1:es.size] do
    let (h, s) := par[t - 1]!
    P := P.push (compS P[h]! sig[s]!)
  return P.toList.map encS

meta def ptsS {n : Nat} (σ : Equiv.Perm (Fin n)) : List Nat := (List.finRange n).map fun i => (σ i).val

meta def genPS : List Nat := [numS pMat1, numS pMat2, numS pMat3]

meta def hqS : List Nat :=
  [numS cMat1, numS dMat1, numS dInvMat1, numS cMat2, numS dMat2, numS dInvMat2,
    numS cMat3, numS dMat3, numS dInvMat3]

meta def genQS : List Nat :=
  (List.range 3).map fun j =>
    mulM (mulM (mulM (hqS.getD (3 * j) 0) (hqS.getD (3 * j + 1) 0)) (hqS.getD (3 * j) 0))
      (hqS.getD (3 * j + 2) 0)

meta def recPS : List Nat := recS genPS 128

meta def recQS : List Nat := recS genQS 64

meta def recTS : List Nat := imgS genPS 128 #[ptsS tPerm1, ptsS tPerm2, ptsS tPerm3]

meta def recUS : List Nat := imgS genQS 64 #[ptsS uPerm1, ptsS uPerm2, ptsS uPerm3]

end CFSG.KD.SylowG2.Gen

#kss_ntree CFSG.KD.SylowG2.RPP CFSG.KD.SylowG2.Gen.recPS
#kss_ntree CFSG.KD.SylowG2.RQQ CFSG.KD.SylowG2.Gen.recQS
#kss_ntree CFSG.KD.SylowG2.HQ CFSG.KD.SylowG2.Gen.hqS
#kss_ntree CFSG.KD.SylowG2.RT CFSG.KD.SylowG2.Gen.recTS
#kss_ntree CFSG.KD.SylowG2.RU CFSG.KD.SylowG2.Gen.recUS
