module

public meta import Lean
meta import Certificates.Data.Foote82OmegaSixClass
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.OmegaSix.Gen

open CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIClassAux CFSG.KD.YamakiRep.Gen

meta def coords : List (Fin 2 ⊕ Fin 2 ⊕ Fin 2) :=
  [.inl 0, .inl 1, .inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1)]

meta def numO (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) : Nat :=
  coords.foldl (fun acc a => coords.foldl (fun acc b =>
    acc ||| ((A a b).val <<< (6 * (bit6 a).val + (bit6 b).val))) acc) 0

meta def hdr : List Nat :=
  [aMat, bMat, rMat, rAMat, rBMat, a6cMat, a6d1Mat, a6d2Mat, e1Mat, e2Mat].map numO

meta def tab : Array Nat × Array (Nat × Nat) × Array Nat × Array Nat :=
  bfsM #[hdr[0]!, hdr[1]!] 25920

meta def recO : List Nat :=
  let (es, par, C, POS) := tab
  if es.size != 25920 then panic! s!"the table has {es.size} elements" else
  let (srt, sri) := sortM es
  let f := fun (v : Nat) (i : Nat) => v <<< (64 + 16 * i)
  hdr ++ (List.range (es.size + 1)).map fun t =>
    let p := par.getD t (0, 0)
    let base := es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 |||
      f (sri.getD t 0) 3
    (List.range 2).foldl (fun acc s =>
      acc ||| f (C.getD (2 * t + s) 0) (4 + s) ||| f (POS.getD (2 * t + s) 0) (6 + s)) base

meta def posO : List Nat :=
  hdr.map fun x => (tab.1.findIdx? (· == x)).getD 0

end CFSG.KD.OmegaSix.Gen

#kss_ntree CFSG.KD.OmegaSix.RO CFSG.KD.OmegaSix.Gen.recO
#kss_ntree CFSG.KD.OmegaSix.ROP CFSG.KD.OmegaSix.Gen.posO
