module

public meta import Lean
meta import Certificates.Data.Foote82OmegaSixClass
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.OmegaSix.GenD

open CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIClassAux CFSG.KD.YamakiRep.Gen

meta def coordsD : List (Fin 2 ⊕ Fin 2 ⊕ Fin 2) :=
  [.inl 0, .inl 1, .inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1)]

meta def numD (A : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) : Nat :=
  coordsD.foldl (fun acc a => coordsD.foldl (fun acc b =>
    acc ||| ((A a b).val <<< (6 * (bit6 a).val + (bit6 b).val))) acc) 0

meta def gensD : List Nat :=
  let a := numD aMat
  let b := numD bMat
  [a, b, a, mulM b (mulM b (mulM b b))]

meta def bfsD (st : Nat → Nat → Nat) (k x fuel : Nat) :
    Array Nat × Array (Nat × Nat) × Array Nat × Array Nat := Id.run do
  let mut es : Array Nat := #[x]
  let mut par : Array (Nat × Nat) := #[]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert x 0
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

meta def recD (hdr : List Nat) (st : Nat → Nat → Nat) (x n : Nat) : List Nat :=
  let (es, par, C, POS) := bfsD st 2 x n
  if es.size != n then panic! s!"the search has {es.size} elements" else
  let (srt, sri) := sortM es
  let f := fun (v : Nat) (i : Nat) => v <<< (64 + 16 * i)
  hdr ++ (List.range (es.size + 1)).map fun t =>
    let p := par.getD t (0, 0)
    let base := es.getD t 0 ||| f p.1 0 ||| f p.2 1 ||| f (srt.getD t 0) 2 |||
      f (sri.getD t 0) 3
    (List.range 2).foldl (fun acc s =>
      acc ||| f (C.getD (2 * t + s) 0) (4 + s) ||| f (POS.getD (2 * t + s) 0) (6 + s)) base

meta def recR : List Nat :=
  let g := gensD.toArray
  recD (gensD ++ [numD rMat]) (fun y s => mulM (mulM g[s]! y) g[2 + s]!) (numD rMat) 36

meta def gensW : List Nat :=
  let c := numD a6cMat
  let d₁ := numD a6d1Mat
  let d₂ := numD a6d2Mat
  [mulM (mulM (mulM c d₁) c) d₁, mulM (mulM (mulM c d₂) c) d₂]

meta def recW : List Nat :=
  let g := gensW.toArray
  recD gensW (fun y s => mulM y g[s]!) oneM 360

end CFSG.KD.OmegaSix.GenD

#kss_ntree CFSG.KD.OmegaSix.RCR CFSG.KD.OmegaSix.GenD.recR
#kss_ntree CFSG.KD.OmegaSix.RW CFSG.KD.OmegaSix.GenD.recW
